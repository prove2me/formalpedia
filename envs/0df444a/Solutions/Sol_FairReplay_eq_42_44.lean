-- Prove2me | solution 1 for FairReplay.eq_42_44
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-11-15T21:30:49.308198+00:00
-- url     : https://prove2.me/submissions/f7c9019e-f7c8-4d43-9a63-d0c9d08aaaf0

import Mathlib
import Definitions.Def_FairReplay_fourWayModel
import Definitions.Def_FairReplay_vertexModel
namespace CarriedFourWay
section
open MeasureTheory InformationTheory
namespace ReplayLaw
open FairReplay
noncomputable section

lemma code (p s d U : ℝ) (hs : 0 ≤ s) (hd : 0 ≤ d) :
    obsCode (fourWayObs ![p,p] ![p+s+d,p+s] U) =
      if U ≤ p then 15 else if U ≤ p+s then 10 else if U ≤ p+s+d then 2 else 0 := by
  by_cases h0 : U ≤ p
  · have h1 : U ≤ p+s := by linarith
    have h2 : U ≤ p+s+d := by linarith
    norm_num [fourWayObs,thresholdOut,obsCode,Fin.sum_univ_succ,h0,h1,h2]
  · by_cases h1 : U ≤ p+s
    · have h2 : U ≤ p+s+d := by linarith
      norm_num [fourWayObs,thresholdOut,obsCode,Fin.sum_univ_succ,h0,h1,h2]
    · by_cases h2 : U ≤ p+s+d
      · norm_num [fourWayObs,thresholdOut,obsCode,Fin.sum_univ_succ,h0,h1,h2]
      · norm_num [fourWayObs,thresholdOut,obsCode,Fin.sum_univ_succ,h0,h1,h2]

lemma interval_mass (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) :
    uniformTape (Set.Ioc a b) = ENNReal.ofReal (b-a) := by
  have hsub : Set.Ioc a b ⊆ Set.Icc (0:ℝ) 1 := by
    intro x hx
    exact ⟨ha.trans hx.1.le,hx.2.trans hb⟩
  rw [uniformTape, Measure.restrict_apply measurableSet_Ioc,
    Set.inter_eq_left.mpr hsub, Real.volume_Ioc]

lemma left_mass (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    uniformTape (Set.Iic a) = ENNReal.ofReal a := by
  have he : Set.Iic a ∩ Set.Icc (0:ℝ) 1 = Set.Icc 0 a := by
    ext x
    simp only [Set.mem_inter_iff,Set.mem_Iic,Set.mem_Icc]
    constructor
    · intro h; exact ⟨h.2.1,h.1⟩
    · intro h; exact ⟨h.2,h.1,h.2.trans ha1⟩
  rw [uniformTape,Measure.restrict_apply measurableSet_Iic,he,Real.volume_Icc]
  simp

lemma right_mass (a : ℝ) (ha : 0 ≤ a) :
    uniformTape (Set.Ioi a) = ENNReal.ofReal (1-a) := by
  have he : Set.Ioi a ∩ Set.Icc (0:ℝ) 1 = Set.Ioc a 1 := by
    ext x
    simp only [Set.mem_inter_iff,Set.mem_Ioi,Set.mem_Icc,Set.mem_Ioc]
    constructor
    · intro h; exact ⟨h.1,h.2.2⟩
    · intro h; exact ⟨h.1,ha.trans h.1.le,h.2⟩
  rw [uniformTape,Measure.restrict_apply measurableSet_Ioi,he,Real.volume_Ioc]

lemma law_atoms (p s d : ℝ) (hp : 0 ≤ p) (hs : 0 ≤ s) (hd : 0 ≤ d) (hpsd : p+s+d ≤ 1) :
    fourWayLaw ![p,p] ![p+s+d,p+s] =
      ENNReal.ofReal p • Measure.dirac 15 + ENNReal.ofReal s • Measure.dirac 10 +
      ENNReal.ofReal d • Measure.dirac 2 + ENNReal.ofReal (1-p-s-d) • Measure.dirac 0 := by
  let f := fun U => obsCode (fourWayObs ![p,p] ![p+s+d,p+s] U)
  have hf : Measurable f := measurable_obsCode.comp (measurable_fourWayObs _ _)
  have h15 : f ⁻¹' {15} = Set.Iic p := by
    ext U
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_Iic]
    dsimp [f]
    rw [code p s d U hs hd]
    split_ifs <;> norm_num <;> (try simp_all) <;> (try constructor) <;> intros <;> linarith
  have h10 : f ⁻¹' {10} = Set.Ioc p (p+s) := by
    ext U
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_Ioc]
    dsimp [f]
    rw [code p s d U hs hd]
    split_ifs <;> norm_num <;> (try simp_all) <;> (try constructor) <;> intros <;> linarith
  have h2 : f ⁻¹' {2} = Set.Ioc (p+s) (p+s+d) := by
    ext U
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_Ioc]
    dsimp [f]
    rw [code p s d U hs hd]
    split_ifs <;> norm_num <;> (try simp_all) <;> (try constructor) <;> intros <;> linarith
  have h0 : f ⁻¹' {0} = Set.Ioi (p+s+d) := by
    ext U
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_Ioi]
    dsimp [f]
    rw [code p s d U hs hd]
    split_ifs <;> norm_num <;> (try simp_all) <;> (try constructor) <;> intros <;> linarith
  have hfinite : ∀ᵐ U ∂uniformTape, f U ∈ ({15,10,2,0} : Finset ℝ) := by
    apply Filter.Eventually.of_forall
    intro U
    dsimp [f]
    rw [code p s d U hs hd]
    split_ifs <;> norm_num
  have hh := (Measure.ae_mem_finset_iff_map_eq_sum_dirac hf.aemeasurable).mp hfinite
  change uniformTape.map f = _
  rw [hh]
  rw [Finset.sum_insert (a := (15:ℝ)) (s := {(10:ℝ),2,0}) (by norm_num),
    Finset.sum_insert (a := (10:ℝ)) (s := {(2:ℝ),0}) (by norm_num),
    Finset.sum_insert (a := (2:ℝ)) (s := {(0:ℝ)}) (by norm_num),Finset.sum_singleton]
  rw [h15,h10,h2,h0,left_mass _ hp (by linarith),interval_mass _ _ hp (by linarith),
    interval_mass _ _ (by linarith) hpsd,right_mass _ (by linarith)]
  have hsub1 : p+s-p = s := by ring
  have hsub2 : p+s+d-(p+s) = d := by ring
  have hsub3 : 1-(p+s+d) = 1-p-s-d := by ring
  rw [hsub1,hsub2,hsub3]
  abel
lemma null_atoms (p s d : ℝ) (hp : 0 ≤ p) (hs : 0 ≤ s) (hps : p+s ≤ 1) :
    (fourWayModel p s d false).P 0 =
      ENNReal.ofReal p • Measure.dirac 15 + ENNReal.ofReal s • Measure.dirac 10 +
        ENNReal.ofReal (1-p-s) • Measure.dirac 0 := by
  have h := law_atoms p s 0 hp hs (by norm_num) (by simpa using hps)
  simpa [fourWayModel] using h

lemma alt_atoms (p s d : ℝ) (hp : 0 ≤ p) (hs : 0 ≤ s) (hd : 0 ≤ d) (hpsd : p+s+d ≤ 1) :
    (fourWayModel p s d true).P 0 =
      ENNReal.ofReal p • Measure.dirac 15 + ENNReal.ofReal s • Measure.dirac 10 +
        ENNReal.ofReal d • Measure.dirac 2 + ENNReal.ofReal (1-p-s-d) • Measure.dirac 0 := by
  exact law_atoms p s d hp hs hd hpsd

lemma integrable_atom (g : ℝ → ℝ) (a c : ℝ) :
    Integrable g (ENNReal.ofReal c • Measure.dirac a) :=
  (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

lemma kl_fourway (p s d : ℝ) (hp : 0 < p) (hs : 0 < s) (hd : 0 < d) (hpsd : p+s+d < 1) :
    klDiv ((fourWayModel p s d false).P 0) ((fourWayModel p s d true).P 0) =
      ENNReal.ofReal ((1-p-s)*Real.log ((1-p-s)/(1-p-s-d))) := by
  let μ := (fourWayModel p s d false).P 0
  let ν := (fourWayModel p s d true).P 0
  let r := 1-p-s
  have hr : 0 < r := by dsimp [r]; linarith
  have hrd : 0 < r-d := by dsimp [r]; linarith
  have hm : μ = ENNReal.ofReal p • Measure.dirac 15 + ENNReal.ofReal s • Measure.dirac 10 +
      ENNReal.ofReal r • Measure.dirac 0 := null_atoms p s d hp.le hs.le (by linarith)
  have hn : ν = ENNReal.ofReal p • Measure.dirac 15 + ENNReal.ofReal s • Measure.dirac 10 +
      ENNReal.ofReal d • Measure.dirac 2 + ENNReal.ofReal (r-d) • Measure.dirac 0 :=
    alt_atoms p s d hp.le hs.le hd.le hpsd.le
  let D : ℝ → ENNReal := fun x => if x = 0 then ENNReal.ofReal r / ENNReal.ofReal (r-d)
    else if x = 2 then 0 else 1
  have hD : Measurable D := by
    exact Measurable.ite (measurableSet_singleton (0:ℝ)) measurable_const
      (Measurable.ite (measurableSet_singleton (2:ℝ)) measurable_const measurable_const)
  have hrd0 : ENNReal.ofReal (r-d) ≠ 0 := (ENNReal.ofReal_pos.mpr hrd).ne'
  have hden : ν.withDensity D = μ := by
    rw [hn,hm]
    norm_num [withDensity_add_measure,withDensity_smul_measure,
      dirac_withDensity,D,smul_smul,ENNReal.mul_div_cancel hrd0 ENNReal.ofReal_ne_top]
  have hac : μ ≪ ν := by
    rw [← hden]
    exact withDensity_absolutelyContinuous ν D
  have hRN := Measure.rnDeriv_withDensity ν hD
  rw [hden] at hRN
  have hllr : llr μ ν =ᵐ[μ] (fun x => Real.log (D x).toReal) := by
    filter_upwards [hac.ae_le hRN] with x hx
    simp only [llr,hx]
  let g := fun x => Real.log (D x).toReal
  have hi : Integrable g μ := by
    rw [hm]
    exact ((integrable_atom g 15 p).add_measure (integrable_atom g 10 s)).add_measure
      (integrable_atom g 0 r)
  have hv : (∫ x,g x ∂μ) = r*Real.log (r/(r-d)) := by
    rw [hm,integral_add_measure ((integrable_atom g 15 p).add_measure (integrable_atom g 10 s))
      (integrable_atom g 0 r),integral_add_measure (integrable_atom g 15 p) (integrable_atom g 10 s)]
    norm_num [integral_smul_measure,integral_dirac,g,D,ENNReal.toReal_div,
      ENNReal.toReal_ofReal hp.le,ENNReal.toReal_ofReal hs.le,ENNReal.toReal_ofReal hr.le,
      ENNReal.toReal_ofReal hrd.le]
  rw [klDiv_of_ac_of_integrable hac (hi.congr hllr.symm),integral_congr_ae hllr]
  change ENNReal.ofReal ((∫ x,g x ∂μ)+ν.real Set.univ-μ.real Set.univ) = _
  rw [hv]
  simp only [measureReal_def,measure_univ,ENNReal.toReal_one,add_sub_cancel_right]
  rfl
end
end ReplayLaw

open FairReplay
theorem solution (p s d : ℝ) (hp : 0 < p) (hs : 0 < s) (hd : 0 < d) (hpsd : p+s+d < 1) :
    let r := 1-p-s
    let μ₀ := (fourWayModel p s d false).P 0
    let μ₁ := (fourWayModel p s d true).P 0
    μ₀ {obsCode (![true,true,true,true] : Fin 4 → Bool)} = ENNReal.ofReal p ∧
      μ₀ {obsCode (![false,true,false,true] : Fin 4 → Bool)} = ENNReal.ofReal s ∧
      μ₀ {obsCode (![false,false,false,false] : Fin 4 → Bool)} = ENNReal.ofReal r ∧
      μ₁ {obsCode (![true,true,true,true] : Fin 4 → Bool)} = ENNReal.ofReal p ∧
      μ₁ {obsCode (![false,true,false,true] : Fin 4 → Bool)} = ENNReal.ofReal s ∧
      μ₁ {obsCode (![false,true,false,false] : Fin 4 → Bool)} = ENNReal.ofReal d ∧
      μ₁ {obsCode (![false,false,false,false] : Fin 4 → Bool)} = ENNReal.ofReal (r-d) ∧
      klDiv μ₀ μ₁ = ENNReal.ofReal (r*Real.log (r/(r-d))) := by
  dsimp only
  have hm := ReplayLaw.null_atoms p s d hp.le hs.le (by linarith)
  have hn := ReplayLaw.alt_atoms p s d hp.le hs.le hd.le hpsd.le
  refine ⟨?_,?_,?_,?_,?_,?_,?_,ReplayLaw.kl_fourway p s d hp hs hd hpsd⟩
  all_goals norm_num [hm,hn,obsCode,Fin.sum_univ_succ]

/-- With zero gap the alternative and null observation laws coincide. -/
theorem zero_gap_control (p s : ℝ) :
    (fourWayModel p s 0 false).P 0 = (fourWayModel p s 0 true).P 0 := by
  simp [fourWayModel]

/-- The equal laws have zero KL even before imposing interior threshold constraints. -/
theorem zero_gap_kl_control (p s : ℝ) :
    klDiv ((fourWayModel p s 0 false).P 0) ((fourWayModel p s 0 true).P 0) = 0 := by
  rw [← zero_gap_control]
  exact klDiv_self _

end
end CarriedFourWay
open MeasureTheory InformationTheory FairReplay
namespace VertexLaw
noncomputable section
lemma code (p s U : ℝ) (hs : 0 ≤ s) :
    obsCode (pairObs p (p+s) U) = if U ≤ p then 3 else if U ≤ p+s then 2 else 0 := by
  by_cases h0 : U ≤ p
  · have h1 : U ≤ p+s := by linarith
    norm_num [pairObs,thresholdOut,obsCode,Fin.sum_univ_succ,h0,h1]
  · by_cases h1 : U ≤ p+s
    · norm_num [pairObs,thresholdOut,obsCode,Fin.sum_univ_succ,h0,h1]
    · norm_num [pairObs,thresholdOut,obsCode,Fin.sum_univ_succ,h0,h1]
lemma law_atoms (p s : ℝ) (hp : 0 ≤ p) (hs : 0 ≤ s) (hps : p+s ≤ 1) :
    pairLaw p (p+s) = ENNReal.ofReal p • Measure.dirac 3 +
      ENNReal.ofReal s • Measure.dirac 2 + ENNReal.ofReal (1-p-s) • Measure.dirac 0 := by
  let f := fun U => obsCode (pairObs p (p+s) U)
  have hf : Measurable f := measurable_obsCode.comp (measurable_pairObs _ _)
  have h3 : f ⁻¹' {3} = Set.Iic p := by
    ext U
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_Iic]
    dsimp [f]
    rw [code p s U hs]
    split_ifs <;> norm_num <;> (try simp_all) <;> (try constructor) <;> intros <;> linarith
  have h2 : f ⁻¹' {2} = Set.Ioc p (p+s) := by
    ext U
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_Ioc]
    dsimp [f]
    rw [code p s U hs]
    split_ifs <;> norm_num <;> (try simp_all) <;> (try constructor) <;> intros <;> linarith
  have h0 : f ⁻¹' {0} = Set.Ioi (p+s) := by
    ext U
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_Ioi]
    dsimp [f]
    rw [code p s U hs]
    split_ifs <;> norm_num <;> (try simp_all) <;> (try constructor) <;> intros <;> linarith
  have hfinite : ∀ᵐ U ∂uniformTape, f U ∈ ({3,2,0} : Finset ℝ) := by
    apply Filter.Eventually.of_forall
    intro U
    dsimp [f]
    rw [code p s U hs]
    split_ifs <;> norm_num
  have hh := (Measure.ae_mem_finset_iff_map_eq_sum_dirac hf.aemeasurable).mp hfinite
  change uniformTape.map f = _
  rw [hh,Finset.sum_insert (a := (3:ℝ)) (s := {(2:ℝ),0}) (by norm_num),
    Finset.sum_insert (a := (2:ℝ)) (s := {(0:ℝ)}) (by norm_num),Finset.sum_singleton]
  rw [h3,h2,h0,CarriedFourWay.ReplayLaw.left_mass _ hp (by linarith),
    CarriedFourWay.ReplayLaw.interval_mass _ _ hp hps,
    CarriedFourWay.ReplayLaw.right_mass _ (by linarith)]
  have he1 : p+s-p = s := by ring
  have he2 : 1-(p+s) = 1-p-s := by ring
  rw [he1,he2]
  abel
lemma null_atoms (p s d : ℝ) (hp : 0 ≤ p) (hs : 0 ≤ s) (hps : p+s ≤ 1) :
    (vertexModel p s d false).P 0 = ENNReal.ofReal p • Measure.dirac 3 +
      ENNReal.ofReal s • Measure.dirac 2 + ENNReal.ofReal (1-p-s) • Measure.dirac 0 := by
  simpa [vertexModel] using law_atoms p s hp hs hps
lemma alt_atoms (p s d : ℝ) (hp : 0 ≤ p) (hsd : 0 ≤ s+d) (hpsd : p+s+d ≤ 1) :
    (vertexModel p s d true).P 0 = ENNReal.ofReal p • Measure.dirac 3 +
      ENNReal.ofReal (s+d) • Measure.dirac 2 + ENNReal.ofReal (1-p-s-d) • Measure.dirac 0 := by
  have h := law_atoms p (s+d) hp hsd (by linarith)
  have he : 1-p-(s+d) = 1-p-s-d := by ring
  simpa [vertexModel,← add_assoc,he] using h
lemma unchanged (p s d : ℝ) :
    (vertexModel p s d false).P 1 = (vertexModel p s d true).P 1 := by
  simp [vertexModel]
lemma unchanged_kl (p s d : ℝ) :
    klDiv ((vertexModel p s d false).P 1) ((vertexModel p s d true).P 1) = 0 := by
  rw [← unchanged]
  exact klDiv_self _
lemma kl_vertex (p s d : ℝ) (hp : 0 < p) (hs : 0 < s) (hd : 0 < d) (hpsd : p+s+d < 1) :
    klDiv ((vertexModel p s d false).P 0) ((vertexModel p s d true).P 0) =
      ENNReal.ofReal (s*Real.log (s/(s+d))+(1-p-s)*Real.log ((1-p-s)/(1-p-s-d))) := by
  let μ := (vertexModel p s d false).P 0
  let ν := (vertexModel p s d true).P 0
  let r := 1-p-s
  have hr : 0 < r := by dsimp [r]; linarith
  have hrd : 0 < r-d := by dsimp [r]; linarith
  have hsd : 0 < s+d := by linarith
  have hm : μ = ENNReal.ofReal p • Measure.dirac 3 + ENNReal.ofReal s • Measure.dirac 2 +
      ENNReal.ofReal r • Measure.dirac 0 := null_atoms p s d hp.le hs.le (by linarith)
  have hn : ν = ENNReal.ofReal p • Measure.dirac 3 + ENNReal.ofReal (s+d) • Measure.dirac 2 +
      ENNReal.ofReal (r-d) • Measure.dirac 0 := alt_atoms p s d hp.le hsd.le hpsd.le
  let D : ℝ → ENNReal := fun x => if x = 0 then ENNReal.ofReal r / ENNReal.ofReal (r-d)
    else if x = 2 then ENNReal.ofReal s / ENNReal.ofReal (s+d) else 1
  have hD : Measurable D := by
    exact Measurable.ite (measurableSet_singleton (0:ℝ)) measurable_const
      (Measurable.ite (measurableSet_singleton (2:ℝ)) measurable_const measurable_const)
  have hrd0 : ENNReal.ofReal (r-d) ≠ 0 := (ENNReal.ofReal_pos.mpr hrd).ne'
  have hsd0 : ENNReal.ofReal (s+d) ≠ 0 := (ENNReal.ofReal_pos.mpr hsd).ne'
  have hden : ν.withDensity D = μ := by
    rw [hn,hm]
    norm_num [withDensity_add_measure,withDensity_smul_measure,
      dirac_withDensity,D,smul_smul,ENNReal.mul_div_cancel hrd0 ENNReal.ofReal_ne_top,
      ENNReal.mul_div_cancel hsd0 ENNReal.ofReal_ne_top]
  have hac : μ ≪ ν := by
    rw [← hden]
    exact withDensity_absolutelyContinuous ν D
  have hRN := Measure.rnDeriv_withDensity ν hD
  rw [hden] at hRN
  have hllr : llr μ ν =ᵐ[μ] (fun x => Real.log (D x).toReal) := by
    filter_upwards [hac.ae_le hRN] with x hx
    simp only [llr,hx]
  let g := fun x => Real.log (D x).toReal
  have hi : Integrable g μ := by
    rw [hm]
    exact ((CarriedFourWay.ReplayLaw.integrable_atom g 3 p).add_measure
      (CarriedFourWay.ReplayLaw.integrable_atom g 2 s)).add_measure
      (CarriedFourWay.ReplayLaw.integrable_atom g 0 r)
  have hv : (∫ x,g x ∂μ) = s*Real.log (s/(s+d))+r*Real.log (r/(r-d)) := by
    rw [hm,integral_add_measure ((CarriedFourWay.ReplayLaw.integrable_atom g 3 p).add_measure
      (CarriedFourWay.ReplayLaw.integrable_atom g 2 s)) (CarriedFourWay.ReplayLaw.integrable_atom g 0 r),
      integral_add_measure (CarriedFourWay.ReplayLaw.integrable_atom g 3 p)
        (CarriedFourWay.ReplayLaw.integrable_atom g 2 s)]
    norm_num [integral_smul_measure,integral_dirac,g,D,ENNReal.toReal_div,
      ENNReal.toReal_ofReal hp.le,ENNReal.toReal_ofReal hs.le,ENNReal.toReal_ofReal hr.le,
      ENNReal.toReal_ofReal hrd.le,ENNReal.toReal_ofReal hsd.le]
  rw [klDiv_of_ac_of_integrable hac (hi.congr hllr.symm),integral_congr_ae hllr]
  change ENNReal.ofReal ((∫ x,g x ∂μ)+ν.real Set.univ-μ.real Set.univ) = _
  rw [hv]
  simp only [measureReal_def,measure_univ,ENNReal.toReal_one,add_sub_cancel_right]
  rfl
end
end VertexLaw

theorem solution (p s d : ℝ) (hp : 0 < p) (hs : 0 < s) (hd : 0 < d) (hpsd : p + s + d < 1) :
    let r := 1 - p - s
    let μ₀ := (vertexModel p s d false).P 0
    let μ₁ := (vertexModel p s d true).P 0
    μ₀ {obsCode (![true, true] : Fin 2 → Bool)} = ENNReal.ofReal p ∧
      μ₀ {obsCode (![false, true] : Fin 2 → Bool)} = ENNReal.ofReal s ∧
      μ₀ {obsCode (![false, false] : Fin 2 → Bool)} = ENNReal.ofReal r ∧
      μ₁ {obsCode (![true, true] : Fin 2 → Bool)} = ENNReal.ofReal p ∧
      μ₁ {obsCode (![false, true] : Fin 2 → Bool)} = ENNReal.ofReal (s + d) ∧
      μ₁ {obsCode (![false, false] : Fin 2 → Bool)} = ENNReal.ofReal (r - d) ∧
      klDiv μ₀ μ₁ = ENNReal.ofReal (s * Real.log (s / (s + d)) + r * Real.log (r / (r - d))) ∧
      (vertexModel p s d false).P 1 = (vertexModel p s d true).P 1 ∧
      klDiv ((vertexModel p s d false).P 1) ((vertexModel p s d true).P 1) = 0 := by
  dsimp only
  have hm := VertexLaw.null_atoms p s d hp.le hs.le (by linarith)
  have hn := VertexLaw.alt_atoms p s d hp.le (by linarith) hpsd.le
  refine ⟨?_,?_,?_,?_,?_,?_,VertexLaw.kl_vertex p s d hp hs hd hpsd,
    VertexLaw.unchanged p s d,VertexLaw.unchanged_kl p s d⟩
  all_goals norm_num [hm,hn,obsCode,Fin.sum_univ_succ]

/-- Without a threshold shift, both actions have identical null and alternative laws. -/
theorem zero_gap_control (p s : ℝ) (i : Fin 2) :
    (vertexModel p s 0 false).P i = (vertexModel p s 0 true).P i := by
  simp [vertexModel]
theorem zero_gap_kl_control (p s : ℝ) (i : Fin 2) :
    klDiv ((vertexModel p s 0 false).P i) ((vertexModel p s 0 true).P i) = 0 := by
  rw [← zero_gap_control]
  exact klDiv_self _
