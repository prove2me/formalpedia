-- Prove2me | solution 1 for GaussLocalMaxColoring.Main.lemma_37
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T19:45:25.263209+00:00
-- url     : https://prove2.me/submissions/42b9225c-f609-4b6a-adfb-77f196046fc4

import Definitions.Def_GaussLocalMaxColoring_Main_Bands
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 2400000


-- Source module: Solutions.GaussLocalMaxCapacity
section
set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem capacity_le_add_two (D ρ : ℝ) : capacity D ρ ≤ D+2 := by
  unfold capacity
  split
  · exact min_le_left _ _
  · split
    · exact min_le_left _ _
    · linarith

theorem capacity_ge_add_one (D ρ : ℝ) (hD : 0 ≤ D) (hρ : ρ∈Set.Icc (-(1/2):ℝ) 1) :
    D+1 ≤ capacity D ρ := by
  have hDD : 0 ≤ D*(D+1) := by positivity
  have hroot (r : ℝ) (hr : 2/3 ≤ r) : D+1 ≤ (1+Real.sqrt (1+6*D*(D+1)*r))/2 := by
    have hrad : (2*D+1)^2 ≤ 1+6*D*(D+1)*r := by
      have h := mul_nonneg hDD (sub_nonneg.mpr hr)
      nlinarith only [h]
    have hnon : 0 ≤ 1+6*D*(D+1)*r := (sq_nonneg _).trans hrad
    have hsq := Real.sq_sqrt hnon
    have hn := Real.sqrt_nonneg (1+6*D*(D+1)*r)
    nlinarith only [hrad,hsq,hn,hD]
  unfold capacity
  split
  · rename_i hρ0
    apply le_min (by linarith)
    apply hroot
    apply (le_div_iff₀ (show 0<1-4*ρ by linarith)).mpr
    nlinarith only [hρ.1]
  · rename_i hρ0
    split
    · rename_i hρ4
      have hρp : 0<ρ := lt_of_not_ge hρ0
      apply le_min (by linarith)
      have h := hroot (1/(1+2*ρ)) (by
        apply (le_div_iff₀ (show 0<1+2*ρ by linarith)).mpr
        nlinarith only [hρ4])
      simpa only [div_eq_mul_inv,one_mul] using h
    · exact le_rfl

theorem capacity_D5_ge (ρ : ℝ) (hρ : ρ∈Set.Icc (-(1/2):ℝ) 1) : D5+1 ≤ capacity D5 ρ := by
  apply capacity_ge_add_one _ _ _ hρ
  norm_num [D5,beta5]

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxCapacityContinuous
section
set_option autoImplicit false
set_option maxHeartbeats 1300000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem capacity_continuousOn (D : ℝ) (hD : 0≤D) :
    ContinuousOn (capacity D) (Set.Icc (-(1/2):ℝ) 1) := by
  let fneg : ℝ → ℝ := fun x => min (D+2) ((1+Real.sqrt (1+6*D*(D+1)*((1-2*x)/(1-4*x))))/2)
  let fpos : ℝ → ℝ := fun x => min (D+2) ((1+Real.sqrt (1+6*D*(D+1)/(1+2*x)))/2)
  let fhi : ℝ → ℝ := fun x => if x≤1/4 then fpos x else D+1
  have hpos : ContinuousOn fpos (Set.Ici (0:ℝ)) := by
    intro x hx
    have hx0 : 0≤x := hx
    have hden : 1+2*x≠0 := by linarith only [hx0]
    apply ContinuousAt.continuousWithinAt
    dsimp only [fpos]
    fun_prop
  have hboundary : fpos (1/4)=D+1 := by
    dsimp only [fpos]
    have he : 1+6*D*(D+1)/(1+2*(1/4:ℝ))=(2*D+1)^2 := by ring
    rw [he,Real.sqrt_sq (by linarith : 0≤2*D+1)]
    rw [min_eq_right (by linarith : (1+(2*D+1))/2≤D+2)]
    ring
  have hhi : ContinuousOn fhi (Set.Ici (0:ℝ)) := by
    apply ContinuousOn.if
    · intro x hx
      have he : x=(1/4:ℝ) := by
        simpa only [show {x : ℝ | x≤1/4}=Set.Iic (1/4) from rfl,frontier_Iic,Set.mem_singleton_iff] using hx.2
      simpa only [he] using hboundary
    · exact hpos.mono Set.inter_subset_left
    · exact continuousOn_const
  have hneg : ContinuousOn fneg (Set.Iic (0:ℝ)) := by
    intro x hx
    have hx0 : x≤0 := hx
    have hden : 1-4*x≠0 := by linarith only [hx0]
    apply ContinuousAt.continuousWithinAt
    dsimp only [fneg]
    fun_prop
  change ContinuousOn (fun x => if x≤0 then fneg x else fhi x) (Set.Icc (-(1/2):ℝ) 1)
  apply ContinuousOn.if
  · intro x hx
    have he : x=0 := by
      simpa only [show {x : ℝ | x≤0}=Set.Iic (0:ℝ) from rfl,frontier_Iic,Set.mem_singleton_iff] using hx.2
    subst x
    simp only [fhi,fneg,fpos,show (0:ℝ)≤1/4 by norm_num,if_pos,mul_zero,sub_zero,div_one,add_zero,mul_one]
  · apply hneg.mono
    intro x hx
    simpa only [show {x : ℝ | x≤0}=Set.Iic (0:ℝ) from rfl,closure_Iic] using hx.2
  · apply hhi.mono
    intro x hx
    have hmem : x∈closure (Set.Ioi (0:ℝ)) := by
      exact (show x∈closure {a : ℝ | 0<a} from by simpa only [not_le] using hx.2)
    simpa only [closure_Ioi] using hmem

theorem capacity_uniformContinuousOn (D : ℝ) (hD : 0≤D) :
    UniformContinuousOn (capacity D) (Set.Icc (-(1/2):ℝ) 1) :=
  isCompact_Icc.uniformContinuousOn_of_continuous (capacity_continuousOn D hD)

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxBandCapacityAlgebra
section
set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

def positiveBandRate (τ D s : ℝ) : ℝ := 2*τ*s*(s+D)/(2*τ*s+D)
def negativeBandRate (τ D s : ℝ) : ℝ := 2*(2*τ-1)*s*(s+D)/((4*s+3*D)*τ-(2*s+D))

theorem positiveBandRate_inversion (τ D s : ℝ) (hτ : 0<τ) (hden : 0<2*τ*s+D)
    (hr : positiveBandRate τ D s≤D+1) :
    s≤(1+Real.sqrt (1+2*D*(D+1)/τ))/2 := by
  have hi := (div_le_iff₀ hden).mp hr
  have hc : τ*(2*D*(D+1)/τ)=2*D*(D+1) := by field_simp
  have hp : τ*((2*s-1)^2-(1+2*D*(D+1)/τ))≤0 := by
    nlinarith only [hi,hc]
  have hsq : (2*s-1)^2≤1+2*D*(D+1)/τ := by
    have hz := nonpos_of_mul_nonpos_right hp hτ
    linarith only [hz]
  have hs := Real.le_sqrt_of_sq_le hsq
  linarith only [hs]

theorem negativeBandRate_den_pos (τ D s : ℝ) (hτ : 1/2<τ) (hD : 0<D) (hs : 0 ≤ s) :
    0<(4*s+3*D)*τ-(2*s+D) := by
  have h1 : 0≤(4*τ-2)*s := mul_nonneg (by linarith only [hτ]) hs
  have h2 : 0<(3*τ-1)*D := mul_pos (by linarith only [hτ]) hD
  nlinarith only [h1,h2]

theorem negativeBandRate_inversion (τ D s : ℝ) (hτ : 1/2<τ)
    (hden : 0<(4*s+3*D)*τ-(2*s+D)) (hr : negativeBandRate τ D s≤D+1) :
    s≤(1+Real.sqrt (1+2*D*(D+1)*(3*τ-1)/(2*τ-1)))/2 := by
  have hi := (div_le_iff₀ hden).mp hr
  have hc : (2*τ-1)*(2*D*(D+1)*(3*τ-1)/(2*τ-1))=2*D*(D+1)*(3*τ-1) := by
    field_simp [show 2*τ-1≠0 by linarith only [hτ]]
  have hp : (2*τ-1)*((2*s-1)^2-(1+2*D*(D+1)*(3*τ-1)/(2*τ-1)))≤0 := by
    nlinarith only [hi,hc]
  have hsq : (2*s-1)^2≤1+2*D*(D+1)*(3*τ-1)/(2*τ-1) := by
    have hz := nonpos_of_mul_nonpos_right hp (show 0<2*τ-1 by linarith only [hτ])
    linarith only [hz]
  have hs := Real.le_sqrt_of_sq_le hsq
  linarith only [hs]

theorem positiveBandRate_vcExp (τ D s : ℝ) (hτ : 0<τ) (hD : 0≤D) (hs : 0<s) :
    s*vcExp (1/τ) (D/s)=positiveBandRate τ D s := by
  have hden : 2*τ*s+D≠0 := (by positivity : 0<2*τ*s+D).ne'
  unfold vcExp positiveBandRate
  field_simp [hτ.ne',hs.ne',hden]
  <;> ring

theorem negativeBandRate_vcExp (τ D s : ℝ) (hτ : 1/2<τ) (hD : 0<D) (hs : 0<s) :
    s*vcExp ((3*τ-1)/(2*τ-1)) (D/s)=negativeBandRate τ D s := by
  have hden : (4*s+3*D)*τ-(2*s+D)≠0 := (negativeBandRate_den_pos τ D s hτ hD hs.le).ne'
  have hτn : 2*τ-1≠0 := by linarith only [hτ]
  have he : 2+((3*τ-1)/(2*τ-1))*(D/s) = ((4*s+3*D)*τ-(2*s+D))/((2*τ-1)*s) := by
    field_simp [hτn,hs.ne']
    <;> ring
  have hk : (3*τ-1)/(2*τ-1)-2=(1-τ)/(2*τ-1) := by
    apply (eq_div_iff hτn).mpr
    rw [sub_mul,div_mul_cancel₀ _ hτn]
    ring
  have hn : ((1-τ)/(2*τ-1)*(D/s))*((2*τ-1)*s)=(1-τ)*D := by
    calc
      ((1-τ)/(2*τ-1)*(D/s))*((2*τ-1)*s) =
          ((1-τ)/(2*τ-1)*(2*τ-1))*((D/s)*s) := by ring
      _ = (1-τ)*D := by rw [div_mul_cancel₀ _ hτn,div_mul_cancel₀ _ hs.ne']
  unfold vcExp negativeBandRate
  rw [he,hk,div_div_eq_mul_div,hn]
  apply (eq_div_iff hden).mpr
  rw [mul_assoc,sub_mul,one_mul,div_mul_cancel₀ _ hden]
  ring

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxBandIdealK
section
set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

def bandIdealK (ρ : ℝ) : ℝ := if ρ≤0 then 3*(1-2*ρ)/(1-4*ρ) else 3/(1+2*ρ)

theorem bandIdealK_bounds (ρ : ℝ) (hρ : ρ∈Set.Icc (-(1/2):ℝ) (1/4)) :
    2≤bandIdealK ρ ∧ bandIdealK ρ≤3 := by
  unfold bandIdealK
  split
  · rename_i hρ0
    have hd : 0<1-4*ρ := by linarith only [hρ0]
    constructor
    · apply (le_div_iff₀ hd).mpr
      linarith only [hρ.1]
    · apply (div_le_iff₀ hd).mpr
      linarith only [hρ0]
  · rename_i hρ0
    have hρp := lt_of_not_ge hρ0
    have hd : 0<1+2*ρ := by linarith only [hρp]
    constructor
    · apply (le_div_iff₀ hd).mpr
      linarith only [hρ.2]
    · apply (div_le_iff₀ hd).mpr
      linarith only [hρp]

theorem bandIdealK_continuousOn : ContinuousOn bandIdealK (Set.Icc (-(1/2):ℝ) (1/4)) := by
  unfold bandIdealK
  apply ContinuousOn.if
  · intro x hx
    have he : x=0 := by
      simpa only [show {x : ℝ | x≤0}=Set.Iic (0:ℝ) from rfl,frontier_Iic,Set.mem_singleton_iff] using hx.2
    simp only [he,mul_zero,sub_zero,add_zero,mul_one,div_one]
  · intro x hx
    have hx0 : x≤0 := by
      simpa only [show {x : ℝ | x≤0}=Set.Iic (0:ℝ) from rfl,closure_Iic,Set.mem_Iic] using hx.2
    have hd : 1-4*x≠0 := by linarith only [hx0]
    apply ContinuousAt.continuousWithinAt
    fun_prop
  · intro x hx
    have hxc : x∈closure (Set.Ioi (0:ℝ)) := by
      exact (show x∈closure {a : ℝ | 0<a} from by simpa only [not_le] using hx.2)
    have hx0 : 0≤x := by simpa only [closure_Ioi,Set.mem_Ici] using hxc
    have hd : 1+2*x≠0 := by linarith only [hx0]
    apply ContinuousAt.continuousWithinAt
    fun_prop

theorem bandIdealK_negative (ρ : ℝ) (hρ : ρ≤0) :
    bandIdealK ρ=(3*((2-2*ρ)/3)-1)/(2*((2-2*ρ)/3)-1) := by
  rw [bandIdealK,if_pos hρ]
  field_simp
  <;> ring

theorem bandIdealK_positive (ρ : ℝ) (hρ : 0<ρ) : bandIdealK ρ=1/((1+2*ρ)/3) := by
  rw [bandIdealK,if_neg (not_le.mpr hρ)]
  field_simp

theorem bandIdealK_rate_above_capacity (D ρ s : ℝ) (hD : 0<D)
    (hρ : ρ∈Set.Icc (-(1/2):ℝ) (1/4)) (hs : 0<s) (hsTop : s≤D+2)
    (hcap : capacity D ρ<s) : D+1<s*vcExp (bandIdealK ρ) (D/s) := by
  by_cases hρ0 : ρ≤0
  · have hτ : 1/2<(2-2*ρ)/3 := by linarith only [hρ0]
    have hroot : (1+Real.sqrt (1+2*D*(D+1)*(3*((2-2*ρ)/3)-1)/(2*((2-2*ρ)/3)-1)))/2=
        (1+Real.sqrt (1+6*D*(D+1)*((1-2*ρ)/(1-4*ρ))))/2 := by
      congr 2
      field_simp
      <;> ring
    rw [capacity,if_pos hρ0,min_lt_iff] at hcap
    have hr : (1+Real.sqrt (1+6*D*(D+1)*((1-2*ρ)/(1-4*ρ))))/2<s :=
      hcap.resolve_left (not_lt.mpr hsTop)
    rw [bandIdealK_negative ρ hρ0,negativeBandRate_vcExp _ D s hτ hD hs]
    by_contra hnot
    have hi := negativeBandRate_inversion _ D s hτ (negativeBandRate_den_pos _ D s hτ hD hs.le) (le_of_not_gt hnot)
    rw [hroot] at hi
    exact (not_le.mpr hr) hi
  · have hρp := lt_of_not_ge hρ0
    have hτ : 0<(1+2*ρ)/3 := by linarith only [hρp]
    have hroot : (1+Real.sqrt (1+2*D*(D+1)/((1+2*ρ)/3)))/2=
        (1+Real.sqrt (1+6*D*(D+1)/(1+2*ρ)))/2 := by
      congr 2
      field_simp
      <;> ring
    rw [capacity,if_neg hρ0,if_pos hρ.2,min_lt_iff] at hcap
    have hr : (1+Real.sqrt (1+6*D*(D+1)/(1+2*ρ)))/2<s := hcap.resolve_left (not_lt.mpr hsTop)
    rw [bandIdealK_positive ρ hρp,positiveBandRate_vcExp _ D s hτ hD.le hs]
    by_contra hnot
    have hi := positiveBandRate_inversion _ D s hτ (by positivity) (le_of_not_gt hnot)
    rw [hroot] at hi
    exact (not_le.mpr hr) hi

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxBandCapacityGap
section
set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem bandIdealRate_continuousOn (D : ℝ) (hD : 0<D) :
    ContinuousOn (fun p : ℝ×ℝ => p.2*vcExp (bandIdealK p.1) (D/p.2))
      (Set.Icc (-(1/2):ℝ) (1/4) ×ˢ Set.Icc (D+1) (D+2)) := by
  let K : Set (ℝ×ℝ) := Set.Icc (-(1/2):ℝ) (1/4) ×ˢ Set.Icc (D+1) (D+2)
  have hk : ContinuousOn (fun p : ℝ×ℝ => bandIdealK p.1) K :=
    bandIdealK_continuousOn.comp continuousOn_fst (fun p hp => hp.1)
  have hb : ContinuousOn (fun p : ℝ×ℝ => D/p.2) K :=
    continuousOn_const.div continuousOn_snd (fun p hp => by linarith only [hp.2.1,hD])
  have hden : ∀p∈K, 2+bandIdealK p.1*(D/p.2)≠0 := by
    intro p hp
    have hs : 0<p.2 := by linarith only [hp.2.1,hD]
    have hk0 := (bandIdealK_bounds p.1 hp.1).1
    have hm : 0 ≤ bandIdealK p.1*(D/p.2) := mul_nonneg (by linarith only [hk0]) (div_nonneg hD.le hs.le)
    linarith only [hm]
  apply continuousOn_snd.mul
  unfold vcExp
  exact continuousOn_const.sub (((hk.sub continuousOn_const).mul hb).div
    (continuousOn_const.add (hk.mul hb)) hden)

theorem band_capacity_uniform_rate_gap (D δ : ℝ) (hD : 0<D) (hδ : 0<δ) :
    ∃σ : ℝ, 0<σ ∧ ∀ρ∈Set.Icc (-(1/2):ℝ) (1/4), ∀s∈Set.Icc (D+1) (D+2),
      capacity D ρ+δ ≤ s → D+1+σ ≤ s*vcExp (bandIdealK ρ) (D/s) := by
  let K : Set (ℝ×ℝ) := Set.Icc (-(1/2):ℝ) (1/4) ×ˢ Set.Icc (D+1) (D+2)
  let f : ℝ×ℝ→ℝ := fun p => capacity D p.1+δ-p.2
  let R : ℝ×ℝ→ℝ := fun p => p.2*vcExp (bandIdealK p.1) (D/p.2)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hcap : ContinuousOn (fun p : ℝ×ℝ => capacity D p.1) K := by
    apply (capacity_continuousOn D hD.le).comp continuousOn_fst
    intro p hp
    exact ⟨hp.1.1,by linarith only [hp.1.2]⟩
  have hf : ContinuousOn f K := (hcap.add continuousOn_const).sub continuousOn_snd
  let B : Set (ℝ×ℝ) := K∩f⁻¹'Set.Iic 0
  have hB : IsCompact B := hf.lowerSemicontinuousOn.isCompact_inter_preimage_Iic hK 0
  have hR : ContinuousOn R B := (bandIdealRate_continuousOn D hD).mono Set.inter_subset_left
  have hstrict : ∀p∈B, D+1<R p := by
    intro p hp
    apply bandIdealK_rate_above_capacity D p.1 p.2 hD hp.1.1
      (by linarith only [hp.1.2.1,hD]) hp.1.2.2
    have hh : capacity D p.1+δ-p.2 ≤ 0 := hp.2
    linarith only [hh,hδ]
  by_cases hNE : B.Nonempty
  · obtain ⟨p,hp,hmin⟩ := hB.exists_isMinOn hNE hR
    refine ⟨(R p-(D+1))/2,by linarith only [hstrict p hp],?_⟩
    intro ρ hρ s hs hcs
    have hx : (ρ,s)∈B := ⟨⟨hρ,hs⟩,by change capacity D ρ+δ-s ≤ 0; linarith only [hcs]⟩
    have hminx : R p≤R (ρ,s) := hmin hx
    have hpos := hstrict p hp
    dsimp only [R] at hminx hpos ⊢
    linarith only [hminx,hpos]
  · refine ⟨1,by norm_num,?_⟩
    intro ρ hρ s hs hcs
    exact False.elim (hNE ⟨(ρ,s),⟨⟨hρ,hs⟩,by change capacity D ρ+δ-s ≤ 0; linarith only [hcs]⟩⟩)

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxBandMass
section
set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem threshold_mass_card {ι : Type*} [DecidableEq ι] (S : Finset ι) (f : ι→ℝ)
    (τ ε err : ℝ) (hτ : 0 ≤ τ) (hf : ∀i∈S,f i ≤ 1)
    (hMass : (τ+ε)*(S.card:ℝ)-err ≤ ∑i∈S,f i) :
    ε*(S.card:ℝ)-err ≤ ((S.filter fun i => τ ≤ f i).card:ℝ) := by
  classical
  have hUpper : (∑i∈S,f i) ≤ ((S.filter fun i => τ ≤ f i).card:ℝ)+τ*(S.card:ℝ) := by
    calc
      (∑i∈S,f i) ≤ ∑i∈S,(((if τ ≤ f i then 1 else 0):ℝ)+τ) := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases h : τ ≤ f i
        · simp only [if_pos h]
          linarith only [hf i hi,hτ]
        · simp only [if_neg h,zero_add]
          exact (lt_of_not_ge h).le
      _ = ((S.filter fun i => τ ≤ f i).card:ℝ)+τ*(S.card:ℝ) := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_boole,Finset.sum_const, nsmul_eq_mul]
        ring
  nlinarith only [hMass,hUpper]

theorem threshold_mass_card_half {ι : Type*} [DecidableEq ι] (S : Finset ι) (f : ι→ℝ)
    (τ ε err : ℝ) (hτ : 0 ≤ τ) (hε : 0 ≤ ε) (herr : err ≤ ε/2) (hf : ∀i∈S,f i ≤ 1)
    (hMass : (τ+ε)*(S.card:ℝ)-err ≤ ∑i∈S,f i) :
    (ε/2)*(S.card:ℝ) ≤ ((S.filter fun i => τ ≤ f i).card:ℝ) := by
  classical
  by_cases hS : S.Nonempty
  · have hCard : (1:ℝ) ≤ S.card := by exact_mod_cast Finset.card_pos.mpr hS
    have h := threshold_mass_card S f τ ε err hτ hf hMass
    have hεCard := mul_le_mul_of_nonneg_left hCard (div_nonneg hε (by norm_num : (0:ℝ) ≤ 2))
    nlinarith only [h,herr,hεCard]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simp

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxBandWitnessNorm
section
set_option autoImplicit false
set_option maxHeartbeats 1300000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem norm_sq_le_one_of_unit_inner {d : ℕ} (e x : Space d) (he : ‖e‖=1)
    (hx : ⟪e,x⟫=‖x‖^2) : ‖x‖^2 ≤ 1 := by
  have h := (le_abs_self ⟪e,x⟫).trans (abs_real_inner_le_norm e x)
  rw [he,one_mul,hx] at h
  nlinarith only [h,norm_nonneg x]

theorem theta_empty_norm_one {n d : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (m : ℕ) (W : WIdx n→Space d) (hT : ThetaFeasible G S m (gram W)) : ‖W none‖=1 := by
  have h : ‖W none‖^2=1 := by simpa only [gram,Matrix.of_apply,real_inner_self_eq_norm_sq] using hT.1
  nlinarith only [h,norm_nonneg (W none)]

theorem theta_one_diag_le_one {n d : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (W : WIdx n→Space d) (hT : ThetaFeasible G S 1 (gram W)) (i : Fin n) (hi : i∈S) :
    (gram W) (some (i,0)) (some (i,0)) ≤ 1 := by
  have h := hT.2.1 i hi (0:Fin 2) (by norm_num)
  have hinner : ⟪W none,W (some (i,0))⟫=‖W (some (i,0))‖^2 := by
    simpa only [gram,Matrix.of_apply,real_inner_self_eq_norm_sq] using h
  have hn := norm_sq_le_one_of_unit_inner (W none) (W (some (i,0))) (theta_empty_norm_one G S 1 W hT) hinner
  simpa only [gram,Matrix.of_apply,real_inner_self_eq_norm_sq] using hn

theorem theta_two_diag_sum_le_one {n d : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (W : WIdx n→Space d) (hT : ThetaFeasible G S 2 (gram W)) (i : Fin n) (hi : i∈S) :
    (gram W) (some (i,0)) (some (i,0))+(gram W) (some (i,1)) (some (i,1)) ≤ 1 := by
  let x := W (some (i,0))+W (some (i,1))
  have h₀ := hT.2.1 i hi (0:Fin 2) (by norm_num)
  have h₁ := hT.2.1 i hi (1:Fin 2) (by norm_num)
  have h01 : ⟪W (some (i,0)),W (some (i,1))⟫=0 := hT.2.2.1 i hi 0 1 (by norm_num) (by norm_num) (by decide)
  have h10 : ⟪W (some (i,1)),W (some (i,0))⟫=0 := by simpa only [real_inner_comm] using h01
  have hx : ‖x‖^2=‖W (some (i,0))‖^2+‖W (some (i,1))‖^2 := by
    rw [← real_inner_self_eq_norm_sq]
    dsimp [x]
    simp only [inner_add_left,inner_add_right,h01,h10,real_inner_self_eq_norm_sq,add_zero,zero_add]
  have heq : ⟪W none,x⟫=‖x‖^2 := by
    dsimp [x]
    rw [inner_add_right]
    change ⟪W none,W (some (i,0))⟫+⟪W none,W (some (i,1))⟫=_
    rw [show ⟪W none,W (some (i,0))⟫=‖W (some (i,0))‖^2 by simpa only [gram,Matrix.of_apply,real_inner_self_eq_norm_sq] using h₀,
      show ⟪W none,W (some (i,1))⟫=‖W (some (i,1))‖^2 by simpa only [gram,Matrix.of_apply,real_inner_self_eq_norm_sq] using h₁]
    exact hx.symm
  have hn := norm_sq_le_one_of_unit_inner (W none) x (theta_empty_norm_one G S 2 W hT) heq
  rw [hx] at hn
  simpa only [gram,Matrix.of_apply,real_inner_self_eq_norm_sq] using hn

theorem positive_band_mass_lower {n d d' : ℕ} (G : SimpleGraph (Fin n)) (Pt : Finset Ival)
    (v : Fin n→Space d) (W : Fin n→Ival→WIdx n→Space d') (hBV : BVGuarantee G Pt v W)
    (r : Fin n) (P : Ival) (hP : P∈Pt) (hPos : P.Positive) (ε : ℝ)
    (hε : 0 ≤ ε) (hτ : 0 ≤ tauPos P ε) (herr : epsSDP n ≤ ε/2) :
    (ε/2)*((band (gram v) r P).card:ℝ) ≤
      ((sPrimePos (band (gram v) r P) (gram (W r P)) (tauPos P ε)).card:ℝ) := by
  have h := (hBV.2 r P hP).1 hPos
  apply threshold_mass_card_half _ _ (tauPos P ε) ε (epsSDP n) hτ hε herr
    (fun i hi => theta_one_diag_le_one G _ (W r P) h.1 i hi)
  rw [show tauPos P ε+ε=(1+2*P.rhoP)/3 by unfold tauPos; ring]
  exact h.2.2.trans h.2.1

theorem negative_band_mass_lower {n d d' : ℕ} (G : SimpleGraph (Fin n)) (Pt : Finset Ival)
    (v : Fin n→Space d) (W : Fin n→Ival→WIdx n→Space d') (hBV : BVGuarantee G Pt v W)
    (r : Fin n) (P : Ival) (hP : P∈Pt) (hNeg : ¬P.Positive) (ε : ℝ)
    (hε : 0 ≤ ε) (hτ : 0 ≤ tauNeg P ε) (herr : epsSDP n ≤ ε/2) :
    (ε/2)*((band (gram v) r P).card:ℝ) ≤
      ((sPrimeNeg (band (gram v) r P) (gram (W r P)) (tauNeg P ε)).card:ℝ) := by
  have h := (hBV.2 r P hP).2 hNeg
  apply threshold_mass_card_half _ _ (tauNeg P ε) ε (epsSDP n) hτ hε herr
    (fun i hi => theta_two_diag_sum_le_one G _ (W r P) h.1 i hi)
  rw [show tauNeg P ε+ε=(2-2*P.rhoP)/3 by unfold tauNeg; ring]
  exact h.2.2.trans h.2.1

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxBandIntervals
section
set_option autoImplicit false
set_option maxHeartbeats 1200000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem Ival.mem_bounds (P : Ival) (x : ℝ) (hx : x∈P.toSet) : P.lo ≤ x ∧ x ≤ P.hi := by
  change (if P.loIn then P.lo ≤ x else P.lo<x) ∧ (if P.hiIn then x ≤ P.hi else x<P.hi) at hx
  split_ifs at hx <;> constructor <;> linarith only [hx.1,hx.2]

theorem Ival.rhoP_bounds (P : Ival) (hP : P.toSet.Nonempty) : P.lo ≤ P.rhoP ∧ P.rhoP ≤ P.hi := by
  have hbLo : BddBelow P.toSet := ⟨P.lo,fun x hx => (P.mem_bounds x hx).1⟩
  have hbHi : BddAbove P.toSet := ⟨P.hi,fun x hx => (P.mem_bounds x hx).2⟩
  obtain ⟨x,hx⟩ := hP
  unfold Ival.rhoP
  split
  · exact ⟨le_csInf ⟨x,hx⟩ (fun y hy => (P.mem_bounds y hy).1),
      (csInf_le hbLo hx).trans (P.mem_bounds x hx).2⟩
  · exact ⟨(P.mem_bounds x hx).1.trans (le_csSup hbHi hx),
      csSup_le ⟨x,hx⟩ (fun y hy => (P.mem_bounds y hy).2)⟩

theorem Ival.rhoP_distance (P : Ival) (x : ℝ) (hx : x∈P.toSet) : |x-P.rhoP| ≤ P.hi-P.lo := by
  have h₁ := P.mem_bounds x hx
  have h₂ := P.rhoP_bounds ⟨x,hx⟩
  apply abs_le.mpr
  constructor <;> linarith only [h₁.1,h₁.2,h₂.1,h₂.2]

theorem band_rhoP_positive_bounds (P : Ival) (hP : P.toSet.Nonempty) (hPos : P.Positive) :
    0 ≤ P.rhoP ∧ P.rhoP ≤ 1 := by
  have hb : BddBelow P.toSet := ⟨0,fun x hx => (hPos hx).1⟩
  obtain ⟨x,hx⟩ := hP
  rw [Ival.rhoP,if_pos hPos]
  exact ⟨le_csInf ⟨x,hx⟩ (fun y hy => (hPos hy).1),(csInf_le hb hx).trans (hPos hx).2⟩

theorem band_rhoP_negative_bounds (P : Ival) (hP : P.toSet.Nonempty)
    (hNeg : ¬P.Positive) (hSubset : P.toSet⊆Set.Icc (-(1/2):ℝ) 0) :
    -(1/2) ≤ P.rhoP ∧ P.rhoP ≤ 0 := by
  have hb : BddAbove P.toSet := ⟨0,fun x hx => (hSubset hx).2⟩
  obtain ⟨x,hx⟩ := hP
  rw [Ival.rhoP,if_neg hNeg]
  exact ⟨(hSubset hx).1.trans (le_csSup hb hx),csSup_le ⟨x,hx⟩ (fun y hy => (hSubset hy).2)⟩

theorem band_threshold_nonnegative (n : ℕ) (Pt : Finset Ival) (hPt : IsBandPartition n Pt)
    (P : Ival) (hP : P∈Pt) (ε : ℝ) (hε : ε ≤ 1/30) :
    (P.Positive → 0 ≤ tauPos P ε) ∧ (¬P.Positive → 0 ≤ tauNeg P ε) := by
  constructor
  · intro hPos
    have hρ := band_rhoP_positive_bounds P (hPt.1 P hP) hPos
    unfold tauPos
    linarith only [hρ.1,hε]
  · intro hNeg
    have hSubset : P.toSet⊆Set.Icc (-(1/2):ℝ) 0 :=
      (hPt.2.2.2.2 P hP).resolve_right hNeg
    have hρ := band_rhoP_negative_bounds P (hPt.1 P hP) hNeg hSubset
    unfold tauNeg
    linarith only [hρ.2,hε]

theorem epsSDP_tendsto_zero : Tendsto epsSDP atTop (𝓝 0) := by
  have harg := (tendsto_natCast_atTop_atTop (R:=ℝ)).const_mul_atTop_of_neg (by norm_num : (-3:ℝ)<0)
  have h := Real.tendsto_exp_atBot.comp harg
  apply h.congr'
  filter_upwards [] with n
  change Real.exp (-3*(n:ℝ))=Real.exp (-(3*(n:ℝ)))
  congr 1
  ring

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxBandCapacityUniform
section
set_option autoImplicit false
set_option maxHeartbeats 1300000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem band_rhoP_in_interval {n : ℕ} (Pt : Finset Ival) (hPt : IsBandPartition n Pt)
    (P : Ival) (hP : P∈Pt) : P.rhoP∈Set.Icc (-(1/2):ℝ) 1 := by
  by_cases hPos : P.Positive
  · have h := band_rhoP_positive_bounds P (hPt.1 P hP) hPos
    exact ⟨by linarith only [h.1],h.2⟩
  · have h := band_rhoP_negative_bounds P (hPt.1 P hP) hPos ((hPt.2.2.2.2 P hP).resolve_right hPos)
    exact ⟨h.1,by linarith only [h.2]⟩

theorem band_capacity_uniform_eventually (D ε : ℝ) (hD : 0≤D) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ∀ Pt : Finset Ival, IsBandPartition n Pt →
      ∀ P∈Pt, ∀ ρ∈P.toSet, |capacity D ρ-capacity D P.rhoP|≤ε := by
  obtain ⟨δ,hδ,hmod⟩ := Metric.uniformContinuousOn_iff_le.mp (capacity_uniformContinuousOn D hD) ε hε
  have hlog : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => 1/Real.log (n:ℝ)) atTop (nhds 0) := tendsto_const_nhds.div_atTop hlog
  filter_upwards [hinv.eventually_lt_const hδ] with n hn
  intro Pt hPt P hP ρ hρ
  have hρBounds : ρ∈Set.Icc (-(1/2):ℝ) 1 := by
    rcases hPt.2.2.2.2 P hP with hS|hS
    · have hh := hS hρ
      exact ⟨hh.1,by linarith only [hh.2]⟩
    · have hh := hS hρ
      exact ⟨by linarith only [hh.1],hh.2⟩
  have hd : dist ρ P.rhoP≤δ := by
    rw [Real.dist_eq]
    exact ((P.rhoP_distance ρ hρ).trans (hPt.2.2.2.1 P hP)).trans hn.le
  simpa only [Real.dist_eq] using hmod ρ hρBounds P.rhoP (band_rhoP_in_interval Pt hPt P hP) hd

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxBandKApprox
section
set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem reciprocal_shift_bound (a ε : ℝ) (ha : 1/3 ≤ a) (ha1 : a ≤ 1/2)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1/30) :
    2 ≤ 1/(a-ε) ∧ 1/(a-ε) ≤ 4 ∧ |1/(a-ε)-1/a| ≤ 100*ε := by
  have ht : 0<a-ε := by linarith only [ha,hε1]
  have ha0 : 0<a := by linarith only [ha]
  have hprod : 1/10 ≤ (a-ε)*a := by
    have hh := mul_le_mul_of_nonneg_left ha (show 0 ≤ a-ε by positivity)
    nlinarith only [hh,ha,hε1]
  refine ⟨(le_div_iff₀ ht).mpr (by linarith only [ha1,hε]),
    (div_le_iff₀ ht).mpr (by linarith only [ha,hε1]),?_⟩
  have hid : 1/(a-ε)-1/a=ε/((a-ε)*a) := by
    rw [div_sub_div _ _ ht.ne' ha0.ne']
    congr 1
    ring
  rw [hid,abs_of_nonneg (div_nonneg hε (by positivity))]
  apply (div_le_iff₀ (mul_pos ht ha0)).mpr
  have hm := mul_le_mul_of_nonneg_left hprod hε
  nlinarith only [hm,hε]

theorem negative_k_shift_bound (a ε : ℝ) (ha : 2/3 ≤ a) (ha1 : a ≤ 1)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1/30) :
    2 ≤ (3*(a-ε)-1)/(2*(a-ε)-1) ∧ (3*(a-ε)-1)/(2*(a-ε)-1) ≤ 4 ∧
      |(3*(a-ε)-1)/(2*(a-ε)-1)-(3*a-1)/(2*a-1)| ≤ 100*ε := by
  have ht : 0<2*(a-ε)-1 := by linarith only [ha,hε1]
  have ha0 : 0<2*a-1 := by linarith only [ha]
  have hprod : 1/20 ≤ (2*(a-ε)-1)*(2*a-1) := by
    have hh := mul_le_mul_of_nonneg_left (show 1/3 ≤ 2*a-1 by linarith only [ha]) ht.le
    nlinarith only [hh,ha,hε1]
  refine ⟨(le_div_iff₀ ht).mpr (by linarith only [ha1,hε]),
    (div_le_iff₀ ht).mpr (by linarith only [ha,hε1]),?_⟩
  have hid : (3*(a-ε)-1)/(2*(a-ε)-1)-(3*a-1)/(2*a-1)=ε/((2*(a-ε)-1)*(2*a-1)) := by
    rw [div_sub_div _ _ ht.ne' ha0.ne']
    congr 1
    ring
  rw [hid,abs_of_nonneg (div_nonneg hε (by positivity))]
  apply (div_le_iff₀ (mul_pos ht ha0)).mpr
  have hm := mul_le_mul_of_nonneg_left hprod hε
  nlinarith only [hm,hε]

theorem bandIdealK_nonnegative (ρ : ℝ) (hρ : 0 ≤ ρ) : bandIdealK ρ=1/((1+2*ρ)/3) := by
  rcases hρ.eq_or_lt with he|hp
  · subst ρ
    norm_num [bandIdealK]
  · exact bandIdealK_positive ρ hp

theorem vcK_bounds_close {n : ℕ} (Pt : Finset Ival) (hPt : IsBandPartition n Pt)
    (P : Ival) (hP : P∈Pt) (hρTop : P.rhoP ≤ 1/4) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1/30) :
    2 ≤ vcK P ε ∧ vcK P ε ≤ 4 ∧ |vcK P ε-bandIdealK P.rhoP| ≤ 100*ε := by
  by_cases hPos : P.Positive
  · have hr := band_rhoP_positive_bounds P (hPt.1 P hP) hPos
    have hb := reciprocal_shift_bound ((1+2*P.rhoP)/3) ε
      (by linarith only [hr.1]) (by linarith only [hρTop]) hε hε1
    simpa only [vcK,if_pos hPos,tauPos,bandIdealK_nonnegative P.rhoP hr.1] using hb
  · have hr := band_rhoP_negative_bounds P (hPt.1 P hP) hPos ((hPt.2.2.2.2 P hP).resolve_right hPos)
    have hb := negative_k_shift_bound ((2-2*P.rhoP)/3) ε
      (by linarith only [hr.2]) (by linarith only [hr.1]) hε hε1
    simpa only [vcK,if_neg hPos,tauNeg,bandIdealK_negative P.rhoP hr.2] using hb

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxBandGrid
section
set_option autoImplicit false
set_option maxHeartbeats 1300000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem kGrid_ge_input (h k : ℝ) (hh : 0<h) : k ≤ kGrid h k := by
  have hc : (k-2)/h ≤ (⌈(k-2)/h⌉:ℤ) := Int.le_ceil _
  have hm : ((⌈(k-2)/h⌉:ℤ):ℝ) ≤ (max 1 ⌈(k-2)/h⌉:ℤ) := by exact_mod_cast le_max_right (1:ℤ) ⌈(k-2)/h⌉
  have hb := (div_le_iff₀ hh).mp (hc.trans hm)
  unfold kGrid
  nlinarith only [hb]

theorem kGrid_le_input_add (h k : ℝ) (hh : 0<h) (hk : 2 ≤ k) : kGrid h k ≤ k+h := by
  have hc : ((⌈(k-2)/h⌉:ℤ):ℝ) ≤ (k-2)/h+1 := (Int.ceil_lt_add_one _).le
  have hm : ((max 1 ⌈(k-2)/h⌉:ℤ):ℝ) ≤ (k-2)/h+1 := by
    rw [Int.cast_max,Int.cast_one]
    exact max_le (by have hq : 0 ≤ (k-2)/h := div_nonneg (by linarith) hh.le; linarith) hc
  have hb := mul_le_mul_of_nonneg_left hm hh.le
  have he : h*((k-2)/h+1)=k-2+h := by field_simp <;> ring
  rw [he] at hb
  unfold kGrid
  linarith only [hb]

def finiteKGrid (h : ℝ) : Finset ℝ := (Finset.Icc (1:ℤ) ⌈3/h⌉).image (fun i : ℤ => 2+h*(i:ℝ))
def finiteBetaGrid (h : ℝ) (N : ℕ) : Finset ℝ := (Finset.Icc (1:ℕ) N).image (fun i : ℕ => h*(i:ℝ))

theorem kGrid_mem_finite (h k : ℝ) (hh : 0<h) (hh1 : h ≤ 1) (hk : k ≤ 4) : kGrid h k∈finiteKGrid h := by
  classical
  have hRatio : (k-2)/h ≤ 3/h := (div_le_div_iff_of_pos_right hh).mpr (by linarith)
  have hCeil : (⌈(k-2)/h⌉:ℤ) ≤ ⌈3/h⌉ := Int.ceil_mono hRatio
  have hOneReal : (1:ℝ) ≤ (⌈3/h⌉:ℤ) :=
    (show (1:ℝ) ≤ 3/h from (le_div_iff₀ hh).mpr (by linarith)).trans (Int.le_ceil _)
  have hOne : (1:ℤ) ≤ ⌈3/h⌉ := by exact_mod_cast hOneReal
  apply Finset.mem_image.mpr
  exact ⟨max 1 ⌈(k-2)/h⌉,Finset.mem_Icc.mpr ⟨le_max_left _ _,max_le hOne hCeil⟩,rfl⟩

theorem maxDegOn_le_card {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : maxDegOn G S ≤ S.card := by
  classical
  apply Finset.sup_le
  intro x hx
  exact Finset.card_le_card (Finset.filter_subset _ _)

theorem betaGrid_mem_finite {n : ℕ} (h : ℝ) (N : ℕ) (hh : 0<h) (hN : h*N=1)
    (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : betaGrid h G S∈finiteBetaGrid h N := by
  classical
  have hN0 : 0<N := by
    by_contra hn
    have hz : N=0 := by omega
    simp only [hz,Nat.cast_zero,mul_zero] at hN
    norm_num at hN
  let A : Set ℕ := {i | 1 ≤ i ∧ (maxDegOn G S:ℝ) ≤ (S.card:ℝ)^(h*i)}
  have hNm : N∈A := by
    refine ⟨by omega,?_⟩
    rw [hN,Real.rpow_one]
    exact_mod_cast maxDegOn_le_card G S
  have hInf : sInf A∈A := Nat.sInf_mem ⟨N,hNm⟩
  have hLe : sInf A ≤ N := Nat.sInf_le hNm
  apply Finset.mem_image.mpr
  exact ⟨(sInf A : ℕ),Finset.mem_Icc.mpr ⟨hInf.1,hLe⟩,rfl⟩

theorem betaGrid_bounds {n : ℕ} (h : ℝ) (N : ℕ) (hh : 0<h) (hN : h*N=1)
    (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : h ≤ betaGrid h G S ∧ betaGrid h G S ≤ 1 := by
  classical
  obtain ⟨i,hi,heq⟩ := Finset.mem_image.mp (betaGrid_mem_finite h N hh hN G S)
  obtain ⟨hi1,hiN⟩ := Finset.mem_Icc.mp hi
  rw [← heq]
  constructor
  · have h : (1:ℝ) ≤ i := by exact_mod_cast hi1
    simpa only [mul_one] using mul_le_mul_of_nonneg_left h hh.le
  · have h : (i:ℝ) ≤ N := by exact_mod_cast hiN
    have hm := mul_le_mul_of_nonneg_left h hh.le
    simpa only [hN] using hm

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxBandGridUniform
section
set_option autoImplicit false
set_option maxHeartbeats 1300000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem littleO_uniform_finite (K B : Finset ℝ) (g : ℝ → ℝ → ℕ → ℝ)
    (hg : ∀ k b, IsLittleO1 (g k b)) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ m : ℕ in atTop, ∀ k ∈ K, ∀ b ∈ B, |g k b m| ≤ ε := by
  apply (K.eventually_all).mpr
  intro k hk
  apply (B.eventually_all).mpr
  intro b hb
  have habs : Tendsto (fun m => |g k b m|) atTop (nhds 0) := by simpa only [abs_zero] using (hg k b).abs
  have h := habs.eventually_lt_const hε
  filter_upwards [h] with m hm
  simpa only [abs_zero] using hm.le

theorem littleO_uniform_grids (h : ℝ) (N : ℕ) (hh : 0<h) (hh1 : h≤1) (hN : h*N=1)
    (g : ℝ → ℝ → ℕ → ℝ) (hg : ∀ k b, IsLittleO1 (g k b)) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ m : ℕ in atTop, ∀ k : ℝ, k≤4 → ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      ∀ S : Finset (Fin n), |g (kGrid h k) (betaGrid h G S) m| ≤ ε := by
  filter_upwards [littleO_uniform_finite (finiteKGrid h) (finiteBetaGrid h N) g hg ε hε] with m hm
  intro k hk n G S
  exact hm _ (kGrid_mem_finite h k hh hh1 hk) _ (betaGrid_mem_finite h N hh hN G S)

theorem betaGrid_le_of_degree {n : ℕ} (h β : ℝ) (hh : 0<h) (hβ : 0≤β)
    (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (hS : S.Nonempty)
    (hd : (maxDegOn G S:ℝ) ≤ (S.card:ℝ)^β) : betaGrid h G S ≤ β+h := by
  classical
  let i : ℕ := max 1 ⌈β/h⌉₊
  have hc : β/h ≤ (i:ℝ) := by
    exact (Nat.le_ceil (β/h)).trans (by exact_mod_cast le_max_right 1 ⌈β/h⌉₊)
  have hβi : β≤h*i := by
    have he := (div_le_iff₀ hh).mp hc
    nlinarith only [he]
  have hi : (i:ℝ) ≤ β/h+1 := by
    dsimp only [i]
    rw [Nat.cast_max,Nat.cast_one]
    apply max_le
    · have hq := div_nonneg hβ hh.le
      linarith only [hq]
    · exact (Nat.ceil_lt_add_one (div_nonneg hβ hh.le)).le
  have hib : h*i≤β+h := by
    have hm := mul_le_mul_of_nonneg_left hi hh.le
    have he : h*(β/h+1)=β+h := by field_simp
    rw [he] at hm
    exact hm
  let A : Set ℕ := {j | 1≤j ∧ (maxDegOn G S:ℝ) ≤ (S.card:ℝ)^(h*j)}
  have hiA : i∈A := by
    refine ⟨le_max_left _ _, hd.trans ?_⟩
    apply Real.rpow_le_rpow_of_exponent_le
    · exact_mod_cast hS.card_pos
    · exact hβi
  have hInf : sInf A ≤ i := Nat.sInf_le hiA
  have hmul := mul_le_mul_of_nonneg_left (show ((sInf A:ℕ):ℝ) ≤ i by exact_mod_cast hInf) hh.le
  change h*(sInf A:ℕ) ≤ β+h
  exact hmul.trans hib

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxBandExponentUniform
section
set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem vcExp_bounds (k b : ℝ) (hk : 2≤k) (hb : 0≤b) : 0≤vcExp k b ∧ vcExp k b≤1 := by
  have hden : 0<2+k*b := by positivity
  unfold vcExp
  constructor
  · have hr : (k-2)*b/(2+k*b)≤1 := by
      apply (div_le_iff₀ hden).mpr
      nlinarith only [hb]
    linarith only [hr]
  · have hr : 0≤(k-2)*b/(2+k*b) := div_nonneg (mul_nonneg (sub_nonneg.mpr hk) hb) hden.le
    linarith only [hr]

theorem vcExp_antitone_beta (k b B : ℝ) (hk : 2≤k) (hb : 0≤b) (hbB : b≤B) : vcExp k B≤vcExp k b := by
  have hB : 0≤B := hb.trans hbB
  have hk0 : 0≤k := by linarith only [hk]
  have hd : 0<2+k*b := by positivity
  have hD : 0<2+k*B := by positivity
  unfold vcExp
  apply sub_le_sub_left
  apply (div_le_div_iff₀ hd hD).mpr
  have hm := mul_nonneg (sub_nonneg.mpr hk) (sub_nonneg.mpr hbB)
  nlinarith only [hm]

theorem vcExp_uniform_modulus (ε : ℝ) (hε : 0<ε) :
    ∃δ : ℝ, 0<δ ∧ ∀k∈Set.Icc (2:ℝ) 5, ∀K∈Set.Icc (2:ℝ) 5,
      ∀b∈Set.Icc (0:ℝ) 2, ∀B∈Set.Icc (0:ℝ) 2,
        |k-K|≤δ → |b-B|≤δ → |vcExp k b-vcExp K B|≤ε := by
  let S : Set (ℝ×ℝ) := Set.Icc (2:ℝ) 5 ×ˢ Set.Icc (0:ℝ) 2
  have hcont : ContinuousOn (fun p : ℝ×ℝ => vcExp p.1 p.2) S := by
    intro p hp
    have hk0 : 0≤p.1 := by linarith only [hp.1.1]
    have hb0 : 0≤p.2 := hp.2.1
    have hden : 2+p.1*p.2≠0 := (by positivity : 0<2+p.1*p.2).ne'
    apply ContinuousAt.continuousWithinAt
    unfold vcExp
    fun_prop
  have hu := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hcont
  obtain ⟨δ,hδ,hm⟩ := Metric.uniformContinuousOn_iff_le.mp hu ε hε
  refine ⟨δ,hδ,?_⟩
  intro k hk K hK b hb B hB hkk hbb
  have hd : dist (k,b) (K,B)≤δ := by
    rw [Prod.dist_eq,max_le_iff]
    simpa only [Real.dist_eq] using And.intro hkk hbb
  simpa only [Real.dist_eq] using hm (k,b) ⟨hk,hb⟩ (K,B) ⟨hK,hB⟩ hd

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxBandDegreeRatio
section
set_option autoImplicit false
set_option maxHeartbeats 1500000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem band_degree_ratio_shift (D s ζ : ℝ) (hD : 0 ≤ D) (hs : D+1 ≤ s)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1/4) :
    0 ≤ D/(s-ζ) ∧ D/(s-ζ) ≤ 1 ∧ 0 ≤ D/(s-ζ)-D/s ∧ D/(s-ζ)-D/s ≤ ζ := by
  have hs0 : 0<s := by linarith only [hs,hD]
  have hs1 : 1 ≤ s := by linarith only [hs,hD]
  have ht : 0<s-ζ := by linarith only [hs1,hζ1]
  have hprod : D ≤ (s-ζ)*s := by
    have hh := mul_le_mul_of_nonneg_left hs1 ht.le
    nlinarith only [hh,hs,hζ1]
  have hid : D/(s-ζ)-D/s=D*ζ/((s-ζ)*s) := by
    rw [div_sub_div _ _ ht.ne' hs0.ne']
    congr 1
    ring
  refine ⟨div_nonneg hD ht.le,(div_le_iff₀ ht).mpr (by linarith only [hs,hζ1]),?_,?_⟩
  · rw [hid]
    positivity
  · rw [hid]
    apply (div_le_iff₀ (mul_pos ht hs0)).mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hprod hζ

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxSection5Scale
section
set_option autoImplicit false
set_option maxHeartbeats 1300000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem section5_log_nat_tendsto_atTop : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem beta5_pos : 0<beta5 := by norm_num [beta5]
theorem beta5_lt_one : beta5<1 := by norm_num [beta5]
theorem D5_pos : 0<D5 := by norm_num [D5,beta5]
theorem eta5_pos : 0<eta5 := by norm_num [eta5]

theorem t5_sq (n : ℕ) (hn : 1≤n) : t5 n^2=(1-beta5)*Real.log (n:ℝ) := by
  apply Real.sq_sqrt
  exact mul_nonneg (sub_nonneg.mpr beta5_lt_one.le) (Real.log_nonneg (by exact_mod_cast hn))

theorem t5_sq_tendsto_atTop : Tendsto (fun n : ℕ => t5 n^2) atTop atTop := by
  apply (section5_log_nat_tendsto_atTop.const_mul_atTop (sub_pos.mpr beta5_lt_one)).congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  exact (t5_sq n hn).symm

theorem t5_tendsto_atTop : Tendsto t5 atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (section5_log_nat_tendsto_atTop.const_mul_atTop (sub_pos.mpr beta5_lt_one))

theorem exp_D5_add_two (n : ℕ) (hn : 1≤n) : Real.exp ((D5+2)*t5 n^2/2)=n := by
  rw [t5_sq n hn]
  have he : (D5+2)*((1-beta5)*Real.log (n:ℝ))/2=Real.log (n:ℝ) := by
    unfold D5
    field_simp [show 1-beta5≠0 from (sub_pos.mpr beta5_lt_one).ne']
    <;> ring
  rw [he,Real.exp_log (by exact_mod_cast (show 0<n by omega))]

theorem degree5_exp (n : ℕ) (hn : 1≤n) : (n:ℝ)^beta5=Real.exp (D5*t5 n^2/2) := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast (show 0<n by omega)),t5_sq n hn]
  congr 1
  unfold D5
  field_simp [show 1-beta5≠0 from (sub_pos.mpr beta5_lt_one).ne']
  <;> ring

theorem capacity_trivial_band_bound {n : ℕ} (hn : 1≤n) (S : Finset (Fin n)) (ρ : ℝ)
    (hcap : D5+2≤capacity D5 ρ+eta5) :
    (S.card:ℝ) ≤ Real.exp ((capacity D5 ρ+eta5)*t5 n^2/2) := by
  have hc : S.card≤n := by simpa only [Fintype.card_fin] using Finset.card_le_univ S
  have hcard : (S.card:ℝ) ≤ n := by exact_mod_cast hc
  rw [←exp_D5_add_two n hn] at hcard
  apply hcard.trans
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcap (sq_nonneg _)) (by norm_num)

theorem target5_le_two_rpow (n : ℕ) (hn : 2≤n) : (target5 n:ℝ) ≤ 2*(n:ℝ)^((1+beta5)/2) := by
  have hn1 : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have hn0 : (0:ℝ)<n := lt_trans zero_lt_one hn1
  have hL0 : 0<numLevels n := Nat.ceil_pos.mpr (Real.log_pos hn1)
  have hL : (1:ℝ)≤numLevels n := by exact_mod_cast hL0
  have hden : 1≤100*(numLevels n:ℝ)^4 := by
    have hpow : (1:ℝ)≤(numLevels n:ℝ)^4 := one_le_pow₀ hL
    linarith only [hpow]
  have hδ : 0≤(n:ℝ)*delta5 n := by unfold delta5; positivity
  have hceil := (Nat.ceil_lt_add_one (show 0≤(n:ℝ)*delta5 n/(100*(numLevels n:ℝ)^4) by positivity)).le
  have hquot : (n:ℝ)*delta5 n/(100*(numLevels n:ℝ)^4)≤(n:ℝ)*delta5 n := div_le_self hδ hden
  have hid : (n:ℝ)*delta5 n=(n:ℝ)^((1+beta5)/2) := by
    unfold delta5
    calc
      (n:ℝ)*(n:ℝ)^(-((1-beta5)/2)) = (n:ℝ)^(1:ℝ)*(n:ℝ)^(-((1-beta5)/2)) := by rw [Real.rpow_one]
      _ = (n:ℝ)^((1+beta5)/2) := by
        rw [←Real.rpow_add hn0]
        congr 1
        ring
  have hpow1 : (1:ℝ)≤(n:ℝ)^((1+beta5)/2) := Real.one_le_rpow hn1.le (by linarith [beta5_pos])
  change (⌈(n:ℝ)*delta5 n/(100*(numLevels n:ℝ)^4)⌉₊:ℝ)≤_
  linarith only [hceil,hquot,hpow1,hid]

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxBandRoundingStable
section
set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem band_rounding_stable (σ : ℝ) (hσ : 0<σ) (hσ1 : σ ≤ 1) :
    ∃ε₀ h₀ ζ : ℝ, 0<ε₀ ∧ 0<h₀ ∧ 0<ζ ∧ ζ ≤ 1/4 ∧
      ∀ε h : ℝ, 0 ≤ ε → ε ≤ ε₀ → ε ≤ 1/30 → 0<h → h ≤ h₀ → h ≤ 1/8 →
      ∀n : ℕ, ∀Pt : Finset Ival, IsBandPartition n Pt → ∀P∈Pt, P.rhoP ≤ 1/4 →
      ∀s∈Set.Icc (D5+1) (D5+2), ∀b∈Set.Icc (0:ℝ) 1,
      b ≤ D5/(s-ζ)+h → ∀err : ℝ, |err| ≤ σ/100 →
      D5+1+σ ≤ s*vcExp (bandIdealK P.rhoP) (D5/s) →
      0 ≤ vcExp (kGrid h (vcK P ε)) b-err ∧
      D5+1+σ/2 ≤ (s-ζ)*(vcExp (kGrid h (vcK P ε)) b-err) := by
  obtain ⟨ξ,hξ,hmod⟩ := vcExp_uniform_modulus (σ/100) (by positivity)
  let ζ : ℝ := min (1/4) (min (ξ/4) (σ/100))
  have hζ : 0<ζ := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hζ1 : ζ ≤ 1/4 := min_le_left _ _
  have hζξ : ζ ≤ ξ/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hζσ : ζ ≤ σ/100 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ξ/400,min (1/8) (ξ/4),ζ,by positivity,lt_min (by norm_num) (by positivity),hζ,hζ1,?_⟩
  intro ε h hε hε0 hε1 hh hh0 hh1 n Pt hPt P hP hρ s hs b hb hbB err herr hgap
  have hhξ : h ≤ ξ/4 := hh0.trans (min_le_right _ _)
  have hρLow := (band_rhoP_in_interval Pt hPt P hP).1
  have hIdealk := bandIdealK_bounds P.rhoP ⟨hρLow,hρ⟩
  have hK := vcK_bounds_close Pt hPt P hP hρ ε hε hε1
  have hk0 : 2 ≤ kGrid h (vcK P ε) := hK.1.trans (kGrid_ge_input h _ hh)
  have hk1 : kGrid h (vcK P ε) ≤ 5 := by
    have hk := kGrid_le_input_add h (vcK P ε) hh hK.1
    linarith only [hk,hK.2.1,hh1]
  have hD : 0 ≤ D5 := D5_pos.le
  have hrat := band_degree_ratio_shift D5 s ζ hD hs.1 hζ.le hζ1
  have hs0 : 0<s := by linarith only [hs.1,D5_pos]
  have hs1 : 1 ≤ s := by linarith only [hs.1,hD]
  have hbase : D5/s∈Set.Icc (0:ℝ) 2 := ⟨by positivity,(div_le_iff₀ hs0).mpr (by linarith only [hs.1,hD])⟩
  let B : ℝ := D5/(s-ζ)+h
  have hB : B∈Set.Icc (0:ℝ) 2 := ⟨by dsimp only [B]; linarith only [hrat.1,hh.le],by dsimp only [B]; linarith only [hrat.2.1,hh1]⟩
  have hkclose : |kGrid h (vcK P ε)-bandIdealK P.rhoP| ≤ ξ := by
    have hgrid : |kGrid h (vcK P ε)-vcK P ε| ≤ h := by
      rw [abs_of_nonneg (sub_nonneg.mpr (kGrid_ge_input h _ hh))]
      linarith only [kGrid_le_input_add h (vcK P ε) hh hK.1]
    have htri := abs_sub_le (kGrid h (vcK P ε)) (vcK P ε) (bandIdealK P.rhoP)
    have hsmall : 100*ε ≤ ξ/4 := by linarith only [hε0]
    linarith only [htri,hgrid,hK.2.2,hsmall,hhξ,hξ]
  have hbclose : |B-D5/s| ≤ ξ := by
    rw [abs_of_nonneg (by dsimp only [B]; linarith only [hrat.2.2.1,hh.le])]
    dsimp only [B]
    linarith only [hrat.2.2.2,hζξ,hhξ,hξ]
  have happrox := hmod _ ⟨hk0,hk1⟩ _ ⟨hIdealk.1,by linarith only [hIdealk.2]⟩ _ hB _ hbase hkclose hbclose
  have hanti := vcExp_antitone_beta (kGrid h (vcK P ε)) b B hk0 hb.1 hbB
  have hbounds := vcExp_bounds (kGrid h (vcK P ε)) b hk0 hb.1
  let I : ℝ := vcExp (bandIdealK P.rhoP) (D5/s)
  let e : ℝ := vcExp (kGrid h (vcK P ε)) b-err
  have heLo : I-2*σ/100 ≤ e := by
    have ha := (abs_le.mp happrox).1
    have he := (abs_le.mp herr).2
    dsimp only [I,e]
    linarith only [ha,hanti,he]
  have heHi : e ≤ 2 := by
    have he := (abs_le.mp herr).1
    dsimp only [e]
    linarith only [hbounds.2,he,hσ1]
  have hILo : 1/2 ≤ I := by
    by_contra hi
    have hil : I ≤ 1/2 := (lt_of_not_ge hi).le
    have hm := mul_le_mul_of_nonneg_left hil hs0.le
    change D5+1+σ ≤ s*I at hgap
    linarith only [hm,hgap,hs.2,hD,hσ]
  have he0 : 0 ≤ e := by linarith only [heLo,hILo,hσ1]
  refine ⟨he0,?_⟩
  have hs7 : s ≤ 7 := by
    have hD5 : D5<5 := by norm_num [D5,beta5]
    linarith only [hs.2,hD5]
  have hdiff : s*(I-e) ≤ 14*σ/100 := by
    have he : I-e ≤ 2*σ/100 := by linarith only [heLo]
    have hm := mul_le_mul_of_nonneg_left he hs0.le
    have htop := mul_le_mul_of_nonneg_right hs7 (show 0 ≤ 2*σ/100 by positivity)
    linarith only [hm,htop]
  have hζe : ζ*e ≤ 2*σ/100 := by
    have hm := mul_le_mul_of_nonneg_left heHi hζ.le
    linarith only [hm,hζσ]
  change D5+1+σ ≤ s*I at hgap
  change D5+1+σ/2 ≤ (s-ζ)*e
  nlinarith only [hgap,hdiff,hζe,hσ]

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxBandMassEventually
section
set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem band_mass_lower_eventually (ε : ℝ) (hε : 0<ε) (hε1 : ε ≤ 1/30) :
    ∀ᶠ n : ℕ in atTop,∀d d' : ℕ,∀G : SimpleGraph (Fin n),∀Pt : Finset Ival,
      IsBandPartition n Pt → ∀v : Fin n→Space d,∀W : Fin n→Ival→WIdx n→Space d',
      BVGuarantee G Pt v W → ∀r : Fin n,∀P : Ival,P∈Pt →
      (P.Positive → (ε/2)*((band (gram v) r P).card:ℝ) ≤
        ((sPrimePos (band (gram v) r P) (gram (W r P)) (tauPos P ε)).card:ℝ)) ∧
      (¬P.Positive → (ε/2)*((band (gram v) r P).card:ℝ) ≤
        ((sPrimeNeg (band (gram v) r P) (gram (W r P)) (tauNeg P ε)).card:ℝ)) := by
  have hErr := epsSDP_tendsto_zero.eventually_lt_const (div_pos hε (by norm_num : (0:ℝ)<2))
  filter_upwards [hErr] with n hErr
  intro d d' G Pt hPt v W hBV r P hP
  have hτ := band_threshold_nonnegative n Pt hPt P hP ε hε1
  exact ⟨fun hPos => positive_band_mass_lower G Pt v W hBV r P hP hPos ε hε.le (hτ.1 hPos) hErr.le,
    fun hNeg => negative_band_mass_lower G Pt v W hBV r P hP hNeg ε hε.le (hτ.2 hNeg) hErr.le⟩

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxBandPositiveIndependent
section
set_option autoImplicit false
set_option maxHeartbeats 1300000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem Ival.rhoP_le_mem (P : Ival) (hPos : P.Positive) (x : ℝ) (hx : x∈P.toSet) : P.rhoP≤x := by
  rw [Ival.rhoP,if_pos hPos]
  exact csInf_le ⟨P.lo,fun y hy => (P.mem_bounds y hy).1⟩ hx

theorem positive_band_independent {n d : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n→Space d)
    (hV : BVVectorConds G (gram v) (epsSDP n)) (r : Fin n) (P : Ival)
    (hPos : P.Positive) (hρ : 1/4<P.rhoP) (hErr : epsSDP n<3/4) :
    IsIndep G (band (gram v) r P) := by
  classical
  intro x hx y hy hxy
  have hxx : P.rhoP≤gram v r x := P.rhoP_le_mem hPos _ (Finset.mem_filter.mp hx).2
  have hyy : P.rhoP≤gram v r y := P.rhoP_le_mem hPos _ (Finset.mem_filter.mp hy).2
  by_cases hrx : r=x
  · subst x
    have he := hV.2.2.1 r y hxy
    linarith only [he,hyy,hρ,hErr]
  by_cases hry : r=y
  · subst y
    have he := hV.2.2.1 r x hxy.symm
    linarith only [he,hxx,hρ,hErr]
  have he := hV.2.2.2.1 x y hxy r hrx hry
  linarith only [he,hxx,hyy,hρ]

theorem isolatedIn_eq_of_independent {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (hS : IsIndep G S) : isolatedIn G S=S := by
  classical
  unfold isolatedIn
  apply Finset.filter_eq_self.mpr
  intro x hx
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hh := Finset.mem_filter.mp hy
  exact hS x hx y hh.1 hh.2

theorem positive_bandOut_card_ge {n d : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n→Space d)
    (hV : BVVectorConds G (gram v) (epsSDP n)) (r : Fin n) (P : Ival)
    (hPos : P.Positive) (hρ : 1/4<P.rhoP) (hErr : epsSDP n<3/4)
    (Y : Matrix (WIdx n) (WIdx n) ℝ) (ε : ℝ) (I' : Finset (Fin n)) :
    (sPrimePos (band (gram v) r P) Y (tauPos P ε)).card≤
      (bandOut G (gram v) r P Y ε I').card := by
  classical
  have hind := positive_band_independent G v hV r P hPos hρ hErr
  have hS : IsIndep G (sPrimePos (band (gram v) r P) Y (tauPos P ε)) := by
    intro x hx y hy
    exact hind x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1
  rw [bandOut,if_pos hPos,isolatedIn_eq_of_independent G _ hS]
  exact Finset.card_le_card Finset.subset_union_left

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxSection5Target
section
set_option autoImplicit false
set_option maxHeartbeats 1300000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem exp_D5_add_one (n : ℕ) (hn : 1≤n) :
    (n:ℝ)^((1+beta5)/2)=Real.exp ((D5+1)*t5 n^2/2) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  rw [Real.rpow_def_of_pos hn0,t5_sq n hn]
  congr 1
  unfold D5
  field_simp [show 1-beta5≠0 from (sub_pos.mpr beta5_lt_one).ne']
  <;> ring

theorem fixed_mul_target5_exponential_upper (A ε : ℝ) (hA : 0≤A) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, A*(target5 n:ℝ) ≤ Real.exp ((D5+1+ε)*t5 n^2/2) := by
  have hexp : Tendsto (fun n : ℕ => Real.exp (ε*t5 n^2/2)) atTop atTop := by
    apply Real.tendsto_exp_atTop.comp
    have h := t5_sq_tendsto_atTop.const_mul_atTop (div_pos hε (by norm_num : (0:ℝ)<2))
    convert h using 1
    ext n
    ring
  filter_upwards [eventually_ge_atTop (2:ℕ),hexp.eventually_ge_atTop (2*A)] with n hn he
  have hT := mul_le_mul_of_nonneg_left (target5_le_two_rpow n hn) hA
  rw [exp_D5_add_one n (by omega)] at hT
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_nonneg ((D5+1)*t5 n^2/2))
  calc
    A*(target5 n:ℝ) ≤ A*(2*Real.exp ((D5+1)*t5 n^2/2)) := hT
    _ = (2*A)*Real.exp ((D5+1)*t5 n^2/2) := by ring
    _ ≤ Real.exp (ε*t5 n^2/2)*Real.exp ((D5+1)*t5 n^2/2) := hm
    _ = Real.exp ((D5+1+ε)*t5 n^2/2) := by
      rw [←Real.exp_add]
      congr 1
      ring

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxBandPositiveBound
section
set_option autoImplicit false
set_option maxHeartbeats 1300000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem positive_band_failed_bound_eventually (ε : ℝ) (hε : 0<ε) (hε1 : ε≤1/30) :
    ∀ᶠ n : ℕ in atTop, ∀d d' : ℕ, ∀G : SimpleGraph (Fin n), ∀Pt : Finset Ival,
      IsBandPartition n Pt → ∀v : Fin n→Space d, ∀W : Fin n→Ival→WIdx n→Space d',
      BVGuarantee G Pt v W → ∀r : Fin n, ∀P∈Pt, P.Positive → 1/4<P.rhoP →
      ∀I' : Finset (Fin n), (bandOut G (gram v) r P (gram (W r P)) ε I').card<target5 n →
      ∀ρ∈P.toSet, ((band (gram v) r P).card:ℝ)≤Real.exp ((capacity D5 ρ+eta5)*t5 n^2/2) := by
  have hscale := fixed_mul_target5_exponential_upper (2/ε) eta5 (by positivity) eta5_pos
  have herr := epsSDP_tendsto_zero.eventually_lt_const (by norm_num : (0:ℝ)<3/4)
  filter_upwards [band_mass_lower_eventually ε hε hε1,hscale,herr] with n hmass hscale herr
  intro d d' G Pt hPt v W hBV r P hP hPos hρ I' hFail ρ hρP
  have hm := (hmass d d' G Pt hPt v W hBV r P hP).1 hPos
  have ho := positive_bandOut_card_ge G v hBV.1 r P hPos hρ herr (gram (W r P)) ε I'
  have hlt : ((sPrimePos (band (gram v) r P) (gram (W r P)) (tauPos P ε)).card:ℝ)<target5 n := by
    exact_mod_cast ho.trans_lt hFail
  have hB : ((band (gram v) r P).card:ℝ)≤(2/ε)*(target5 n:ℝ) := by
    apply (mul_le_mul_iff_right₀ (div_pos hε (by norm_num : (0:ℝ)<2))).mp
    have he : (ε/2)*((2/ε)*(target5 n:ℝ))=target5 n := by field_simp
    rw [he]
    exact hm.trans hlt.le
  have hρgt : 1/4<ρ := hρ.trans_le (P.rhoP_le_mem hPos ρ hρP)
  have hcap : capacity D5 ρ=D5+1 := by
    unfold capacity
    rw [if_neg (by linarith only [hρgt] : ¬ρ≤0),if_neg (not_le.mpr hρgt)]
  rw [hcap]
  exact hB.trans hscale

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxBandInputCount
section
set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem vcInput_subset_band {n : ℕ} (G : SimpleGraph (Fin n)) (X : Matrix (Fin n) (Fin n) ℝ)
    (r : Fin n) (P : Ival) (Y : Matrix (WIdx n) (WIdx n) ℝ) (ε : ℝ) :
    vcInput G X r P Y ε⊆band X r P := by
  classical
  unfold vcInput
  split
  · exact Finset.Subset.trans Finset.sdiff_subset (Finset.filter_subset _ _)
  · exact Finset.filter_subset _ _

theorem maxDegOn_mono {n : ℕ} (G : SimpleGraph (Fin n)) (S T : Finset (Fin n)) (hST : S⊆T) :
    maxDegOn G S  ≤  maxDegOn G T := by
  classical
  apply Finset.sup_le
  intro x hx
  have hn : nbr G S x⊆nbr G T x := Finset.filter_subset_filter _ hST
  exact (Finset.card_le_card hn).trans (Finset.le_sup (f:=fun y => (nbr G T y).card) (hST hx))

theorem vcInput_degree_bound {n : ℕ} (G : SimpleGraph (Fin n)) (X : Matrix (Fin n) (Fin n) ℝ)
    (r : Fin n) (P : Ival) (Y : Matrix (WIdx n) (WIdx n) ℝ) (ε : ℝ) (b : ℝ)
    (hd : (maxDegOn G Finset.univ:ℝ) ≤ (n:ℝ)^b) :
    (maxDegOn G (vcInput G X r P Y ε):ℝ) ≤ (n:ℝ)^b := by
  have hm := maxDegOn_mono G (vcInput G X r P Y ε) Finset.univ (Finset.subset_univ _)
  have hr : (maxDegOn G (vcInput G X r P Y ε):ℝ) ≤ maxDegOn G Finset.univ := by exact_mod_cast hm
  exact hr.trans hd

theorem vcInput_card_lower_of_mass {n : ℕ} (G : SimpleGraph (Fin n))
    (X : Matrix (Fin n) (Fin n) ℝ) (r : Fin n) (P : Ival)
    (Y : Matrix (WIdx n) (WIdx n) ℝ) (ε a : ℝ) (I' : Finset (Fin n)) (T : ℕ)
    (hPos : P.Positive → a*(band X r P).card ≤ (sPrimePos (band X r P) Y (tauPos P ε)).card)
    (hNeg : ¬P.Positive → a*(band X r P).card ≤ (sPrimeNeg (band X r P) Y (tauNeg P ε)).card)
    (hFail : (bandOut G X r P Y ε I').card<T) :
    a*(band X r P).card-T ≤ ((vcInput G X r P Y ε).card:ℝ) := by
  classical
  by_cases hP : P.Positive
  · have hi : isolatedIn G (sPrimePos (band X r P) Y (tauPos P ε))⊆sPrimePos (band X r P) Y (tauPos P ε) := Finset.filter_subset _ _
    have hic := Finset.card_le_card hi
    have ho : (isolatedIn G (sPrimePos (band X r P) Y (tauPos P ε))).card ≤ (bandOut G X r P Y ε I').card := by
      rw [bandOut,if_pos hP]
      exact Finset.card_le_card Finset.subset_union_left
    have hio : ((isolatedIn G (sPrimePos (band X r P) Y (tauPos P ε))).card:ℝ) ≤ T := by
      exact_mod_cast (ho.trans_lt hFail).le
    rw [vcInput,if_pos hP,Finset.card_sdiff_of_subset hi,Nat.cast_sub hic]
    linarith only [hPos hP,hio]
  · rw [vcInput,if_neg hP]
    have hT : (0:ℝ) ≤ T := Nat.cast_nonneg _
    linarith only [hNeg hP,hT]

theorem vcInput_card_lower_eventually (ε : ℝ) (hε : 0<ε) (hε1 : ε ≤ 1/30) :
    ∀ᶠ n : ℕ in atTop, ∀d d' : ℕ, ∀G : SimpleGraph (Fin n), ∀Pt : Finset Ival,
      IsBandPartition n Pt → ∀v : Fin n→Space d, ∀W : Fin n→Ival→WIdx n→Space d',
      BVGuarantee G Pt v W → ∀r : Fin n, ∀P∈Pt, ∀I' : Finset (Fin n),
      (bandOut G (gram v) r P (gram (W r P)) ε I').card<target5 n →
      (ε/2)*((band (gram v) r P).card:ℝ)-(target5 n:ℝ) ≤ 
        ((vcInput G (gram v) r P (gram (W r P)) ε).card:ℝ) := by
  filter_upwards [band_mass_lower_eventually ε hε hε1] with n hn
  intro d d' G Pt hPt v W hBV r P hP I' hFail
  have hm := hn d d' G Pt hPt v W hBV r P hP
  exact vcInput_card_lower_of_mass G (gram v) r P (gram (W r P)) ε (ε/2) I' (target5 n) hm.1 hm.2 hFail

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxBandInputGrowth
section
set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem band_input_size_eventually (ε ζ : ℝ) (hε : 0 < ε) (hζ : 0 < ζ) (M : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ B m : ℕ,
      Real.exp ((D5+1+eta5/4)*t5 n^2/2) ≤ (B:ℝ) →
      (ε/2)*(B:ℝ)-(target5 n:ℝ) ≤ m →
      (ε/4)*(B:ℝ) ≤ m ∧ M ≤ m ∧ Real.exp (Real.log (B:ℝ)-ζ*t5 n^2/2) ≤ m := by
  have hD : 0 < D5 := D5_pos
  have hη : 0 < eta5 := eta5_pos
  have htarget := fixed_mul_target5_exponential_upper (4/ε) (eta5/4) (by positivity) (by positivity)
  have hGrow : Tendsto (fun n : ℕ => (ε/4)*Real.exp ((D5+1+eta5/4)*t5 n^2/2)) atTop atTop := by
    apply Tendsto.const_mul_atTop (by positivity)
    apply Real.tendsto_exp_atTop.comp
    have hh := t5_sq_tendsto_atTop.const_mul_atTop (show 0 < (D5+1+eta5/4)/2 by positivity)
    convert hh using 1
    ext n
    ring
  have hShrink : Tendsto (fun n : ℕ => Real.exp (-ζ*t5 n^2/2)) atTop (nhds 0) := by
    apply Real.tendsto_exp_atBot.comp
    have hh := t5_sq_tendsto_atTop.const_mul_atTop_of_neg (show -ζ/2 < 0 by linarith only [hζ])
    convert hh using 1
    ext n
    ring
  filter_upwards [htarget,hGrow.eventually_ge_atTop (M:ℝ),hShrink.eventually_lt_const (div_pos hε (by norm_num : (0:ℝ) < 4))] with n hT hGrow hShrink
  intro B m hB hm
  have hB0 : (0:ℝ) < B := (Real.exp_pos _).trans_le hB
  have hTB : (target5 n:ℝ) ≤ (ε/4)*(B:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left (hT.trans hB) (div_nonneg hε.le (by norm_num : (0:ℝ) ≤ 4))
    have he : (ε/4)*((4/ε)*(target5 n:ℝ))=target5 n := by field_simp
    rw [he] at hh
    exact hh
  have hsmall : (ε/4)*(B:ℝ) ≤ m := by linarith only [hm,hTB]
  refine ⟨hsmall,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_left hB (div_nonneg hε.le (by norm_num : (0:ℝ) ≤ 4))
    have hMm : (M:ℝ) ≤ m := hGrow.trans (hh.trans hsmall)
    exact_mod_cast hMm
  · rw [Real.exp_sub,Real.exp_log hB0]
    have hmul : (B:ℝ)/Real.exp (ζ*t5 n^2/2) ≤ (ε/4)*(B:ℝ) := by
      calc
        (B:ℝ)/Real.exp (ζ*t5 n^2/2) = (B:ℝ)*Real.exp (-ζ*t5 n^2/2) := by rw [div_eq_mul_inv,←Real.exp_neg]; congr 1; congr 1; ring
        _  ≤  (B:ℝ)*(ε/4) := mul_le_mul_of_nonneg_left hShrink.le hB0.le
        _ = (ε/4)*(B:ℝ) := by ring
    exact hmul.trans hsmall

 theorem band_degree_rpow_bound (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm : 0  <  m)
    (s ζ : ℝ) (hsζ : 0  <  s-ζ)
    (hsize : Real.exp ((s-ζ)*t5 n^2/2) ≤ (m:ℝ)) :
    (n:ℝ)^beta5 ≤ (m:ℝ)^(D5/(s-ζ)) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hlog := Real.log_le_log (Real.exp_pos _) hsize
  rw [Real.log_exp] at hlog
  have hmul := mul_le_mul_of_nonneg_right hlog (div_nonneg D5_pos.le hsζ.le)
  have he : ((s-ζ)*t5 n^2/2)*(D5/(s-ζ))=D5*t5 n^2/2 := by
    field_simp [hsζ.ne']
    <;> ring
  rw [he] at hmul
  rw [degree5_exp n hn,Real.rpow_def_of_pos hm0]
  exact Real.exp_le_exp.mpr hmul

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxLemma37
section
set_option autoImplicit false
set_option maxHeartbeats 2400000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main

/-- **Lemma 37** (Band bound after failed rounding; p. 38, PDF 40). Section 5 setting, with the
rounding slack `ε_thr` and the grid step `h` sufficiently small (depending only on `β`, `η`) and
`n` sufficiently large (depending on the `o(1)` family `g` of VectorColoring's guarantee): for
every band `S = S_{r,P}`, if the band rounding returns `FAIL` (its set has size ` <  T`) and its
internal call to VectorColoring meets its guarantee, then `|S|  ≤  exp((C_D(ρ) + η) t²/2)` for
every `ρ ∈ P`. -/
theorem lemma_37 :
    ∃ ε₀ h₀ : ℝ, 0  <  ε₀ ∧ 0  <  h₀ ∧
      ∀ εthr h : ℝ, 0  <  εthr → εthr  ≤  ε₀ → εthr  ≤  1 / 30 → 0  <  h → h  ≤  h₀ → h  ≤  1 / 8 →
      (∃ N : ℕ, h * N = 1) →
      ∀ g : ℝ → ℝ → ℕ → ℝ, (∀ k b, IsLittleO1 (g k b)) →
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀  ≤  n →
      ∀ (d d' : ℕ) (G : SimpleGraph (Fin n)), G.Colorable 3 →
        (maxDegOn G Finset.univ : ℝ)  ≤  (n : ℝ) ^ beta5 →
        ∀ (Pt : Finset Ival), IsBandPartition n Pt →
        ∀ (v : Fin n → Space d) (W : Fin n → Ival → WIdx n → Space d'), BVGuarantee G Pt v W →
        ∀ (r : Fin n) (P : Ival), P ∈ Pt →
        ∀ I' : Finset (Fin n),
          VCMeets g h (vcK P εthr) G (vcInput G (gram v) r P (gram (W r P)) εthr) I' →
          (bandOut G (gram v) r P (gram (W r P)) εthr I').card  <  target5 n →
          ∀ ρ ∈ P.toSet,
            ((band (gram v) r P).card : ℝ)  ≤  Real.exp ((capacity D5 ρ + eta5) * t5 n ^ 2 / 2) := by
  obtain ⟨σ₀,hσ₀,hgap₀⟩ := band_capacity_uniform_rate_gap D5 (eta5/2) D5_pos (by have h := eta5_pos; positivity)
  let σ : ℝ := min σ₀ 1
  have hσ : 0 < σ := lt_min hσ₀ (by norm_num)
  have hσ1 : σ ≤ 1 := min_le_right _ _
  have hgap : ∀ρ∈Set.Icc (-(1/2):ℝ) (1/4), ∀s∈Set.Icc (D5+1) (D5+2),
      capacity D5 ρ+eta5/2 ≤ s → D5+1+σ ≤ s*vcExp (bandIdealK ρ) (D5/s) := by
    intro ρ hρ s hs hc
    have hg := hgap₀ ρ hρ s hs hc
    have hm : σ ≤ σ₀ := min_le_left _ _
    linarith only [hg,hm]
  obtain ⟨ε₀,h₀,ζ,hε₀,hh₀,hζ,hζ1,hstable⟩ := band_rounding_stable σ hσ hσ1
  refine ⟨ε₀,h₀,hε₀,hh₀,?_⟩
  intro ε h hε hε0 hε1 hh hh0 hh1 hN g hg
  obtain ⟨N,hN⟩ := hN
  have hgGrid := littleO_uniform_grids h N hh (by linarith only [hh1]) hN g hg (σ/100) (by positivity)
  obtain ⟨M,hM⟩ := eventually_atTop.mp hgGrid
  have hCount := vcInput_card_lower_eventually ε hε hε1
  have hSize := band_input_size_eventually ε ζ hε hζ (max 1 M)
  have hPositive := positive_band_failed_bound_eventually ε hε hε1
  have hCapacity := band_capacity_uniform_eventually D5 (eta5/4) D5_pos.le (by have h := eta5_pos; positivity)
  have hTarget := fixed_mul_target5_exponential_upper 1 (σ/4) (by norm_num) (by positivity)
  have hAll := hCount.and (hSize.and (hPositive.and (hCapacity.and (hTarget.and (eventually_ge_atTop (2:ℕ))))))
  obtain ⟨N₀,hAll⟩ := eventually_atTop.mp hAll
  refine ⟨N₀,?_⟩
  intro n hn d d' G hColor hDegree Pt hPt v W hBV r P hP I' hVC hFail ρ hρ
  obtain ⟨hCount,hSize,hPositive,hCapacity,hTarget,hn2⟩ := hAll n hn
  by_cases hSpecial : P.Positive ∧ 1/4 < P.rhoP
  · exact hPositive d d' G Pt hPt v W hBV r P hP hSpecial.1 hSpecial.2 I' hFail ρ hρ
  have hρTop : P.rhoP ≤ 1/4 := by
    by_cases hPos : P.Positive
    · exact le_of_not_gt (fun hp => hSpecial ⟨hPos,hp⟩)
    · have hr := band_rhoP_negative_bounds P (hPt.1 P hP) hPos ((hPt.2.2.2.2 P hP).resolve_right hPos)
      linarith only [hr.2]
  by_contra hBad
  have hBad : Real.exp ((capacity D5 ρ+eta5)*t5 n^2/2) < ((band (gram v) r P).card:ℝ) := lt_of_not_ge hBad
  let S := band (gram v) r P
  let Q := vcInput G (gram v) r P (gram (W r P)) ε
  let B : ℕ := S.card
  let m : ℕ := Q.card
  let u : ℝ := t5 n^2/2
  let s : ℝ := Real.log (B:ℝ)/u
  have hnReal : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hu : 0 < u := by
    dsimp only [u]
    rw [t5_sq n (by omega)]
    exact div_pos (mul_pos (sub_pos.mpr beta5_lt_one) (Real.log_pos hnReal)) (by norm_num)
  have hB0 : (0:ℝ) < B := (Real.exp_pos _).trans hBad
  have hslog : s*u=Real.log (B:ℝ) := div_mul_cancel₀ _ hu.ne'
  have hsBad : capacity D5 ρ+eta5 < s := by
    apply (lt_div_iff₀ hu).mpr
    have hh := Real.log_lt_log (Real.exp_pos _) hBad
    rw [Real.log_exp] at hh
    have he : (capacity D5 ρ+eta5)*t5 n^2/2=(capacity D5 ρ+eta5)*u := by dsimp only [u]; ring
    rw [he] at hh
    exact hh
  have hcapDist := hCapacity Pt hPt P hP ρ hρ
  have hsCap : capacity D5 P.rhoP+eta5/2 ≤ s := by
    have hd := (abs_le.mp hcapDist).1
    have hη := eta5_pos
    linarith only [hd,hsBad,hη]
  have hρP := band_rhoP_in_interval Pt hPt P hP
  have hcapLow := capacity_D5_ge P.rhoP hρP
  have hsLow : D5+1 ≤ s := by have hη := eta5_pos; linarith only [hsCap,hcapLow,hη]
  have hBn : B ≤ n := by simpa only [B,S,Fintype.card_fin] using Finset.card_le_univ S
  have hlogn : Real.log (n:ℝ)=(D5+2)*u := by
    have hh := congrArg Real.log (exp_D5_add_two n (by omega))
    rw [Real.log_exp] at hh
    calc
      Real.log (n:ℝ) = (D5+2)*t5 n^2/2 := hh.symm
      _ = (D5+2)*u := by dsimp only [u]; ring
  have hsTop : s ≤ D5+2 := by
    apply (div_le_iff₀ hu).mpr
    rw [←hlogn]
    exact Real.log_le_log hB0 (by exact_mod_cast hBn)
  have hBbig : Real.exp ((D5+1+eta5/4)*t5 n^2/2) ≤ (B:ℝ) := by
    have hsRate : D5+1+eta5/4 ≤ s := by have hη := eta5_pos; linarith only [hsCap,hcapLow,hη]
    have hm := mul_le_mul_of_nonneg_right hsRate hu.le
    rw [hslog] at hm
    calc
      Real.exp ((D5+1+eta5/4)*t5 n^2/2) = Real.exp ((D5+1+eta5/4)*u) := by congr 1; dsimp only [u]; ring
      _  ≤  Real.exp (Real.log (B:ℝ)) := Real.exp_le_exp.mpr hm
      _ = (B:ℝ) := Real.exp_log hB0
  have hcount : (ε/2)*(B:ℝ)-(target5 n:ℝ) ≤ m := hCount d d' G Pt hPt v W hBV r P hP I' hFail
  have hsize := hSize B m hBbig hcount
  have hmPos : 0  <  m := lt_of_lt_of_le (by omega : 0  <  max 1 M) hsize.2.1
  have hQ : Q.Nonempty := Finset.card_pos.mp hmPos
  have hsz : Real.exp ((s-ζ)*t5 n^2/2) ≤ (m:ℝ) := by
    convert hsize.2.2 using 1
    congr 1
    rw [←hslog]
    dsimp only [u]
    ring
  have hsζ : 0 < s-ζ := by have hD := D5_pos; linarith only [hsLow,hζ1,hD]
  have hdQ : (maxDegOn G Q:ℝ) ≤ (m:ℝ)^(D5/(s-ζ)) := by
    exact (vcInput_degree_bound G (gram v) r P (gram (W r P)) ε beta5 hDegree).trans
      (band_degree_rpow_bound n (by omega) m hmPos s ζ hsζ hsz)
  have hbGrid := betaGrid_bounds h N hh hN G Q
  have hbLow : 0 ≤ betaGrid h G Q := hh.le.trans hbGrid.1
  have hbUpper := betaGrid_le_of_degree h (D5/(s-ζ)) hh (div_nonneg D5_pos.le hsζ.le) G Q hQ hdQ
  have hK := vcK_bounds_close Pt hPt P hP hρTop ε hε.le hε1
  have hgSmall : |g (kGrid h (vcK P ε)) (betaGrid h G Q) m| ≤ σ/100 :=
    hM m ((le_max_right 1 M).trans hsize.2.1) (vcK P ε) hK.2.1 n G Q
  have hRate := hgap P.rhoP ⟨hρP.1,hρTop⟩ s ⟨hsLow,hsTop⟩ hsCap
  have hstab := hstable ε h hε.le hε0 hε1 hh hh0 hh1 n Pt hPt P hP hρTop s ⟨hsLow,hsTop⟩
    (betaGrid h G Q) ⟨hbLow,hbGrid.2⟩ hbUpper (g (kGrid h (vcK P ε)) (betaGrid h G Q) m) hgSmall hRate
  let e : ℝ := vcExp (kGrid h (vcK P ε)) (betaGrid h G Q)-g (kGrid h (vcK P ε)) (betaGrid h G Q) m
  have hpower : Real.exp ((s-ζ)*t5 n^2/2)^e ≤ (m:ℝ)^e :=
    Real.rpow_le_rpow (Real.exp_nonneg _) hsz hstab.1
  rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp] at hpower
  have hCall : (m:ℝ)^e ≤ (I'.card:ℝ) := hVC.2.2 hQ
  have hOut : I'.card ≤ (bandOut G (gram v) r P (gram (W r P)) ε I').card := by
    classical
    unfold bandOut
    split
    · exact Finset.card_le_card Finset.subset_union_right
    · exact le_rfl
  have hOutReal : (I'.card:ℝ) < target5 n := by exact_mod_cast hOut.trans_lt hFail
  have hFinal : Real.exp ((D5+1+σ/2)*u) < Real.exp ((D5+1+σ/4)*u) := by
    calc
      Real.exp ((D5+1+σ/2)*u)  ≤  Real.exp (((s-ζ)*t5 n^2/2)*e) := by
        apply Real.exp_le_exp.mpr
        have hm := mul_le_mul_of_nonneg_right hstab.2 hu.le
        have he : ((s-ζ)*(vcExp (kGrid h (vcK P ε)) (betaGrid h G Q)-g (kGrid h (vcK P ε)) (betaGrid h G Q) m))*u=
            ((s-ζ)*t5 n^2/2)*e := by dsimp only [u,e]; ring
        rw [he] at hm
        exact hm
      _  ≤  (m:ℝ)^e := hpower
      _  ≤  (I'.card:ℝ) := hCall
      _  <  (target5 n:ℝ) := hOutReal
      _  ≤  Real.exp ((D5+1+σ/4)*u) := by
        have he : (D5+1+σ/4)*t5 n^2/2=(D5+1+σ/4)*u := by dsimp only [u]; ring
        simpa only [one_mul,he] using hTarget
  have hStrict : Real.exp ((D5+1+σ/4)*u) < Real.exp ((D5+1+σ/2)*u) :=
    Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_right (by linarith only [hσ]) hu)
  exact (not_lt_of_ge hStrict.le) hFinal

end GaussLocalMaxColoring.Main

end

#print axioms GaussLocalMaxColoring.Main.lemma_37


open GaussLocalMaxColoring.Main RecGaussColoring.Main
open scoped RealInnerProductSpace

theorem solution :
    ∃ ε₀ h₀ : ℝ, 0 < ε₀ ∧ 0 < h₀ ∧
      ∀ εthr h : ℝ, 0 < εthr → εthr ≤ ε₀ → εthr ≤ 1 / 30 → 0 < h → h ≤ h₀ → h ≤ 1 / 8 →
      (∃ N : ℕ, h * N = 1) →
      ∀ g : ℝ → ℝ → ℕ → ℝ, (∀ k b, IsLittleO1 (g k b)) →
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ (d d' : ℕ) (G : SimpleGraph (Fin n)), G.Colorable 3 →
        (maxDegOn G Finset.univ : ℝ) ≤ (n : ℝ) ^ beta5 →
        ∀ (Pt : Finset Ival), IsBandPartition n Pt →
        ∀ (v : Fin n → Space d) (W : Fin n → Ival → WIdx n → Space d'), BVGuarantee G Pt v W →
        ∀ (r : Fin n) (P : Ival), P ∈ Pt →
        ∀ I' : Finset (Fin n),
          VCMeets g h (vcK P εthr) G (vcInput G (gram v) r P (gram (W r P)) εthr) I' →
          (bandOut G (gram v) r P (gram (W r P)) εthr I').card < target5 n →
          ∀ ρ ∈ P.toSet,
            ((band (gram v) r P).card : ℝ) ≤ Real.exp ((capacity D5 ρ + eta5) * t5 n ^ 2 / 2) := GaussLocalMaxColoring.Main.lemma_37

#print axioms solution
