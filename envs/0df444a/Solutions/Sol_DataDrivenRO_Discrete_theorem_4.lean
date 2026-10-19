-- Prove2me | solution 1 for DataDrivenRO.Discrete.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-18T05:50:34.524053+00:00
-- url     : https://prove2.me/submissions/738fa7bf-88f7-4352-8c47-a53c171657ac

-- Licensed under Apache 2.0. Complete finite-support robust risk theorem.
import Mathlib
import Definitions.Def_DataDrivenRO_Discrete_Setting


namespace DiscreteROProof

lemma chi_zero (t : ℝ) : (t - 0)^2 / (2*t) = t/2 := by
  by_cases ht : t = 0
  · simp [ht]
  · field_simp
    ring

lemma chi_expand {a t : ℝ} (ht : 0 < t) :
    (t-a)^2/(2*t) = t/2-a+a^2/(2*t) := by
  field_simp
  ring

lemma inverse_mix {x y b c : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hbc : b+c=1) :
    1/(b*x+c*y) ≤ b/x+c/y := by
  have hw : 0 < b*x+c*y := by
    rcases lt_or_eq_of_le hb with hb | rfl
    · positivity
    · simp_all
  have he : (b/x+c/y-1/(b*x+c*y))*(x*y*(b*x+c*y)) =
      b*c*(x-y)^2 := by
    have hcval : c = 1-b := by linarith
    field_simp [hx.ne', hy.ne', hw.ne']
    rw [hcval]
    ring
  have hn : 0 ≤ b*c*(x-y)^2 := by positivity
  have hp : 0 < x*y*(b*x+c*y) := by positivity
  nlinarith

lemma chi_mix {a x y b c : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hax : x=0 → a=0) (hay : y=0 → a=0)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hbc : b+c=1) :
    ((b*x+c*y)-a)^2/(2*(b*x+c*y)) ≤
      b*((x-a)^2/(2*x))+c*((y-a)^2/(2*y)) := by
  by_cases ha0 : a=0
  · simp only [ha0, chi_zero]
    ring_nf
    exact le_rfl
  have hx0 : 0 < x := lt_of_le_of_ne hx (Ne.symm (fun h => ha0 (hax h)))
  have hy0 : 0 < y := lt_of_le_of_ne hy (Ne.symm (fun h => ha0 (hay h)))
  have hw : 0 < b*x+c*y := by
    rcases lt_or_eq_of_le hb with hb | rfl
    · positivity
    · simp_all
  rw [chi_expand hw, chi_expand hx0, chi_expand hy0]
  have hi := mul_le_mul_of_nonneg_left (inverse_mix hx0 hy0 hb hc hbc)
    (show 0 ≤ a^2/2 by positivity)
  have he : b*a+c*a=a := by rw [← add_mul, hbc, one_mul]
  simp only [div_eq_mul_inv, mul_inv_rev] at hi ⊢
  nlinarith [hi]

lemma entropy_lower {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t)
    (hpos : 0 < a → 0 < t) : a-t ≤ a*Real.log (a/t) := by
  by_cases ha0 : a=0
  · simp [ha0, ht]
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have ht' := hpos ha'
  have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos ht' ha')) ha
  rw [Real.log_div ht'.ne' ha0] at h
  rw [Real.log_div ha0 ht'.ne']
  have he : a*(t/a-1)=t-a := by field_simp
  rw [he] at h
  nlinarith

lemma entropy_mix {a x y b c : ℝ} (ha : 0 ≤ a)
    (hax : 0<a → 0<x) (hay : 0<a → 0<y)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hbc : b+c=1) :
    a*Real.log (a/(b*x+c*y)) ≤
      b*(a*Real.log (a/x))+c*(a*Real.log (a/y)) := by
  by_cases ha0 : a=0
  · simp [ha0]
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hx' := hax ha'
  have hy' := hay ha'
  have hw : 0 < b*x+c*y := by
    rcases lt_or_eq_of_le hb with hb | rfl
    · positivity
    · simp_all
  have hh := strictConcaveOn_log_Ioi.concaveOn.2 hx' hy' hb hc hbc
  simp only [smul_eq_mul] at hh
  rw [Real.log_div ha0 hw.ne', Real.log_div ha0 hx'.ne', Real.log_div ha0 hy'.ne']
  have he : b*(a*Real.log a)+c*(a*Real.log a)=a*Real.log a := by
    rw [← add_mul, hbc, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hh ha]

end DiscreteROProof


namespace DiscreteROProof
open Set DataDrivenRO.Discrete

lemma chi2_center {n : ℕ} {h : Fin n → ℝ} {ρ : ℝ}
    (hh : h ∈ stdSimplex ℝ (Fin n)) (hρ : 0 ≤ ρ) : h ∈ chi2Region h ρ := by
  exact ⟨hh, fun _ hi => hi, by simpa using hρ⟩

lemma chi2_convex {n : ℕ} (h : Fin n → ℝ) (ρ : ℝ) :
    Convex ℝ (chi2Region h ρ) := by
  intro x hx y hy b c hb hc hbc
  have hm := convex_stdSimplex ℝ (Fin n) hx.1 hy.1 hb hc hbc
  refine ⟨hm, ?_, ?_⟩
  · intro i hi
    change b*x i+c*y i=0 at hi
    by_cases hbi : b=0
    · have hc1 : c=1 := by linarith
      exact hy.2.1 i (by simpa [hbi, hc1] using hi)
    · have hxi : x i=0 := by
        have := mul_nonneg hc (hy.1.1 i)
        have := mul_nonneg hb (hx.1.1 i)
        have := (lt_of_le_of_ne hb (Ne.symm hbi))
        nlinarith
      exact hx.2.1 i hxi
  · change (∑ i, (b*x i+c*y i-h i)^2/(2*(b*x i+c*y i))) ≤ ρ
    calc
      _ ≤ ∑ i, (b*((x i-h i)^2/(2*x i))+c*((y i-h i)^2/(2*y i))) :=
        Finset.sum_le_sum fun i _ => chi_mix (hx.1.1 i) (hy.1.1 i)
          (hx.2.1 i) (hy.2.1 i) hb hc hbc
      _ = b*(∑ i, (x i-h i)^2/(2*x i))+c*(∑ i, (y i-h i)^2/(2*y i)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ b*ρ+c*ρ := add_le_add (mul_le_mul_of_nonneg_left hx.2.2 hb)
        (mul_le_mul_of_nonneg_left hy.2.2 hc)
      _ = ρ := by rw [← add_mul, hbc, one_mul]

noncomputable def chiFloor (a ρ : ℝ) : ℝ := a^2/(2*(ρ+a))

lemma chiFloor_pos {a ρ : ℝ} (ha : 0<a) (hρ : 0≤ρ) : 0<chiFloor a ρ := by
  unfold chiFloor
  positivity

lemma chi2_floor {n : ℕ} {h p : Fin n → ℝ} {ρ : ℝ}
    (hp : p ∈ chi2Region h ρ) (i : Fin n) (ha : 0<h i) :
    chiFloor (h i) ρ ≤ p i := by
  have hpi : 0<p i := lt_of_le_of_ne (hp.1.1 i)
    (Ne.symm (fun hi => ha.ne' (hp.2.1 i hi)))
  have hterm : (p i-h i)^2/(2*p i) ≤ ρ :=
    (Finset.single_le_sum (fun j _ => div_nonneg (sq_nonneg (p j-h j)) (mul_nonneg (by norm_num) (hp.1.1 j)))
      (Finset.mem_univ i)).trans hp.2.2
  have hρ : 0≤ρ := (div_nonneg (sq_nonneg (p i-h i)) (by positivity)).trans hterm
  have hd : 0<2*(ρ+h i) := by positivity
  rw [chiFloor, div_le_iff₀ hd]
  have ht := (div_le_iff₀ (show 0<2*p i by positivity)).mp hterm
  nlinarith [sq_nonneg (p i)]

noncomputable def chiExtension {n : ℕ} (h : Fin n → ℝ) (ρ : ℝ) (p : Fin n → ℝ) : ℝ :=
  ∑ i, if 0<h i then (p i-h i)^2/(2*max (chiFloor (h i) ρ) (p i)) else p i/2

lemma chiExtension_continuous {n : ℕ} {h : Fin n → ℝ} {ρ : ℝ}
    (hρ : 0≤ρ) : Continuous (chiExtension h ρ) := by
  classical
  apply continuous_finsetSum
  intro i _
  by_cases hi : 0<h i
  · simp only [if_pos hi]
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro p
      have : 0 < max (chiFloor (h i) ρ) (p i) :=
        (chiFloor_pos hi hρ).trans_le (le_max_left _ _)
      positivity
  · simp only [if_neg hi]
    fun_prop

lemma chi2_compact {n : ℕ} {h : Fin n → ℝ} {ρ : ℝ}
    (hh : h ∈ stdSimplex ℝ (Fin n)) (hρ : 0≤ρ) : IsCompact (chi2Region h ρ) := by
  classical
  let B : Set (Fin n → ℝ) := {p | ∀ i, 0<h i → chiFloor (h i) ρ ≤ p i}
  have hB : IsClosed B := by
    have he : B = (⋂ i, ⋂ (_ : 0<h i), {p : Fin n → ℝ | chiFloor (h i) ρ ≤ p i}) := by
      ext p
      simp [B]
    rw [he]
    exact isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_le continuous_const (continuous_apply i)
  have hext {p : Fin n → ℝ} (hp : p ∈ B) :
      chiExtension h ρ p = ∑ i, (p i-h i)^2/(2*p i) := by
    unfold chiExtension
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 0<h i
    · simp only [if_pos hi, max_eq_right (hp i hi)]
    · have hi0 : h i=0 := le_antisymm (le_of_not_gt hi) (hh.1 i)
      simpa [hi0] using (chi_zero (p i)).symm
  have heq : chi2Region h ρ =
      (stdSimplex ℝ (Fin n) ∩ B) ∩ {p | chiExtension h ρ p ≤ ρ} := by
    ext p
    constructor
    · intro hp
      have hb : p ∈ B := fun i hi => chi2_floor hp i hi
      exact ⟨⟨hp.1, hb⟩, by change chiExtension h ρ p ≤ ρ; rw [hext hb]; exact hp.2.2⟩
    · rintro ⟨⟨hp, hb⟩, hc⟩
      refine ⟨hp, ?_, ?_⟩
      · intro i hi
        by_contra hne
        have hhpos : 0<h i := lt_of_le_of_ne (hh.1 i) (Ne.symm hne)
        have := hb i hhpos
        have := chiFloor_pos hhpos hρ
        linarith
      · change chiExtension h ρ p ≤ ρ at hc
        rwa [hext hb] at hc
  rw [heq]
  exact ((isCompact_stdSimplex ℝ (Fin n)).inter_right hB).inter_right
    (isClosed_le (chiExtension_continuous hρ) continuous_const)

lemma chi2_geometry {n : ℕ} {phat : Fin n → ℝ} {ρ : ℝ}
    (hphat : phat ∈ stdSimplex ℝ (Fin n)) (hρ : 0≤ρ) :
    (chi2Region phat ρ).Nonempty ∧ Convex ℝ (chi2Region phat ρ) ∧
      IsCompact (chi2Region phat ρ) :=
  ⟨⟨phat, chi2_center hphat hρ⟩, chi2_convex phat ρ, chi2_compact hphat hρ⟩

end DiscreteROProof


namespace DiscreteROProof
open Set DataDrivenRO.Discrete RobustMDP.EntropyInner

lemma g_center {n : ℕ} {h : Fin n → ℝ} {ρ : ℝ}
    (hh : h ∈ stdSimplex ℝ (Fin n)) (hρ : 0≤ρ) : h ∈ gRegion h ρ := by
  refine ⟨hh, fun _ hi => hi, ?_⟩
  have he : klDiv h h=0 := by
    unfold klDiv
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : h i=0
    · simp [hi]
    · simp [hi]
  simpa [he] using hρ

lemma g_convex {n : ℕ} {h : Fin n → ℝ} (hh : h ∈ stdSimplex ℝ (Fin n))
    (ρ : ℝ) : Convex ℝ (gRegion h ρ) := by
  intro x hx y hy b c hb hc hbc
  refine ⟨convex_stdSimplex ℝ (Fin n) hx.1 hy.1 hb hc hbc, ?_, ?_⟩
  · intro i hi
    change 0<b*x i+c*y i
    have hx' := hx.2.1 i hi
    have hy' := hy.2.1 i hi
    rcases lt_or_eq_of_le hb with hb | rfl
    · positivity
    · simp_all
  · change (∑ i, h i*Real.log (h i/(b*x i+c*y i))) ≤ ρ
    calc
      _ ≤ ∑ i, (b*(h i*Real.log (h i/x i))+c*(h i*Real.log (h i/y i))) :=
        Finset.sum_le_sum fun i _ => entropy_mix (hh.1 i) (hx.2.1 i) (hy.2.1 i) hb hc hbc
      _ = b*klDiv h x+c*klDiv h y := by
        simp only [klDiv, Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ b*ρ+c*ρ := add_le_add (mul_le_mul_of_nonneg_left hx.2.2 hb)
        (mul_le_mul_of_nonneg_left hy.2.2 hc)
      _ = ρ := by rw [← add_mul, hbc, one_mul]

noncomputable def gFloor (a ρ : ℝ) : ℝ := a*Real.exp (-(ρ+1)/a)

lemma gFloor_pos {a : ℝ} (ha : 0<a) (ρ : ℝ) : 0<gFloor a ρ := by
  unfold gFloor
  positivity

lemma g_floor {n : ℕ} {h p : Fin n → ℝ} {ρ : ℝ}
    (hh : h ∈ stdSimplex ℝ (Fin n)) (hp : p ∈ gRegion h ρ)
    (i : Fin n) (ha : 0<h i) : gFloor (h i) ρ ≤ p i := by
  have hn (j : Fin n) : 0≤h j*Real.log (h j/p j)-(h j-p j) :=
    sub_nonneg.mpr (entropy_lower (hh.1 j) (hp.1.1 j) (hp.2.1 j))
  have hs := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hn j) (Finset.mem_univ i)
  have hsum : (∑ j, (h j*Real.log (h j/p j)-(h j-p j))) = klDiv h p := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hh.2, hp.1.2]
    simp [klDiv]
  rw [hsum] at hs
  have ha1 := (mem_Icc_of_mem_stdSimplex hh i).2
  have hp0 := hp.1.1 i
  have ht : h i*Real.log (h i/p i) ≤ ρ+1 := by linarith [hp.2.2]
  have hlog : Real.log (h i)+(-(ρ+1)/(h i)) ≤ Real.log (p i) := by
    rw [Real.log_div ha.ne' (hp.2.1 i ha).ne'] at ht
    have hquot : Real.log (h i)-Real.log (p i) ≤ (ρ+1)/(h i) :=
      (le_div_iff₀ ha).mpr (by nlinarith [ht])
    rw [neg_div]
    linarith
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_add, Real.exp_log ha, Real.exp_log (hp.2.1 i ha)] at he
  exact he

noncomputable def gExtension {n : ℕ} (h : Fin n → ℝ) (ρ : ℝ) (p : Fin n → ℝ) : ℝ :=
  ∑ i, if 0<h i then h i*Real.log (h i/max (gFloor (h i) ρ) (p i)) else 0

lemma gExtension_continuous {n : ℕ} (h : Fin n → ℝ) (ρ : ℝ) :
    Continuous (gExtension h ρ) := by
  classical
  apply continuous_finsetSum
  intro i _
  by_cases hi : 0<h i
  · simp only [if_pos hi]
    apply Continuous.mul continuous_const
    apply Continuous.log
    · apply Continuous.div continuous_const
      · fun_prop
      · intro p
        exact ne_of_gt ((gFloor_pos hi ρ).trans_le (le_max_left _ _))
    · intro p
      exact ne_of_gt (div_pos hi ((gFloor_pos hi ρ).trans_le (le_max_left _ _)))
  · simp only [if_neg hi]
    exact continuous_const

lemma g_compact {n : ℕ} {h : Fin n → ℝ} {ρ : ℝ}
    (hh : h ∈ stdSimplex ℝ (Fin n)) : IsCompact (gRegion h ρ) := by
  classical
  let B : Set (Fin n → ℝ) := {p | ∀ i, 0<h i → gFloor (h i) ρ ≤ p i}
  have hB : IsClosed B := by
    have he : B = (⋂ i, ⋂ (_ : 0<h i), {p : Fin n → ℝ | gFloor (h i) ρ ≤ p i}) := by
      ext p
      simp [B]
    rw [he]
    exact isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_le continuous_const (continuous_apply i)
  have hext {p : Fin n → ℝ} (hp : p ∈ B) : gExtension h ρ p = klDiv h p := by
    unfold gExtension klDiv
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 0<h i
    · simp only [if_pos hi, max_eq_right (hp i hi)]
    · have hi0 : h i=0 := le_antisymm (le_of_not_gt hi) (hh.1 i)
      simp [hi0]
  have heq : gRegion h ρ =
      (stdSimplex ℝ (Fin n) ∩ B) ∩ {p | gExtension h ρ p ≤ ρ} := by
    ext p
    constructor
    · intro hp
      have hb : p ∈ B := fun i hi => g_floor hh hp i hi
      exact ⟨⟨hp.1, hb⟩, by change gExtension h ρ p ≤ ρ; rw [hext hb]; exact hp.2.2⟩
    · rintro ⟨⟨hp, hb⟩, hc⟩
      refine ⟨hp, fun i hi => (gFloor_pos hi ρ).trans_le (hb i hi), ?_⟩
      change gExtension h ρ p ≤ ρ at hc
      rwa [hext hb] at hc
  rw [heq]
  exact ((isCompact_stdSimplex ℝ (Fin n)).inter_right hB).inter_right
    (isClosed_le (gExtension_continuous h ρ) continuous_const)

lemma g_geometry {n : ℕ} {phat : Fin n → ℝ} {ρ : ℝ}
    (hphat : phat ∈ stdSimplex ℝ (Fin n)) (hρ : 0≤ρ) :
    (gRegion phat ρ).Nonempty ∧ Convex ℝ (gRegion phat ρ) ∧
      IsCompact (gRegion phat ρ) :=
  ⟨⟨phat, g_center hphat hρ⟩, g_convex hphat ρ, g_compact hphat⟩

end DiscreteROProof


namespace DiscreteROProof
open Set
open DataDrivenRO.Discrete

noncomputable def weightedPoint {d n : ℕ} (a : Fin n → (Fin d → ℝ))
    (q : Fin n → ℝ) : Fin d → ℝ := ∑ j, q j • a j

def liftedSet {d n : ℕ} (a : Fin n → (Fin d → ℝ))
    (R : Set (Fin n → ℝ)) (ε : ℝ) : Set (Fin d → ℝ) :=
  {u | ∃ q ∈ stdSimplex ℝ (Fin n), ∃ p ∈ R,
    (∀ j, q j ≤ p j / ε) ∧ u = weightedPoint a q}

lemma weightedPoint_continuous {d n : ℕ} (a : Fin n → (Fin d → ℝ)) :
    Continuous (weightedPoint a) := by
  exact continuous_finsetSum _ fun j _ => (continuous_apply j).smul continuous_const

lemma weightedPoint_mix {d n : ℕ} (a : Fin n → (Fin d → ℝ))
    (q r : Fin n → ℝ) (b c : ℝ) :
    weightedPoint a (b • q + c • r) = b • weightedPoint a q + c • weightedPoint a r := by
  simp only [weightedPoint, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul,
    mul_smul, Finset.sum_add_distrib, Finset.smul_sum]

lemma liftedSet_nonempty {d n : ℕ} (a : Fin n → (Fin d → ℝ))
    {R : Set (Fin n → ℝ)} (hne : R.Nonempty) (hR : R ⊆ stdSimplex ℝ (Fin n))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) : (liftedSet a R ε).Nonempty := by
  obtain ⟨p, hp⟩ := hne
  refine ⟨weightedPoint a p, p, hR hp, p, hp, ?_, rfl⟩
  intro j
  apply (le_div_iff₀ hε).2
  nlinarith [(hR hp).1 j]

lemma liftedSet_convex {d n : ℕ} (a : Fin n → (Fin d → ℝ))
    {R : Set (Fin n → ℝ)} (hR : Convex ℝ R) {ε : ℝ} (hε : 0 < ε) :
    Convex ℝ (liftedSet a R ε) := by
  rintro u ⟨q,hq,p,hp,hqp,rfl⟩ v ⟨r,hr,s,hs,hrs,rfl⟩ b c hb hc hbc
  refine ⟨b • q + c • r, convex_stdSimplex ℝ (Fin n) hq hr hb hc hbc,
    b • p + c • s, hR hp hs hb hc hbc, ?_, ?_⟩
  · intro j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    apply (le_div_iff₀ hε).2
    have hq' := (le_div_iff₀ hε).1 (hqp j)
    have hr' := (le_div_iff₀ hε).1 (hrs j)
    nlinarith [mul_nonneg hb (sub_nonneg.mpr hq'), mul_nonneg hc (sub_nonneg.mpr hr')]
  · exact (weightedPoint_mix a q r b c).symm

lemma liftedSet_compact {d n : ℕ} (a : Fin n → (Fin d → ℝ))
    {R : Set (Fin n → ℝ)} (hR : IsCompact R) {ε : ℝ} (hε : 0 < ε) :
    IsCompact (liftedSet a R ε) := by
  let K : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    (stdSimplex ℝ (Fin n) ×ˢ R) ∩ ⋂ j, {z | ε * z.1 j ≤ z.2 j}
  have hK : IsCompact K := by
    apply ((isCompact_stdSimplex ℝ (Fin n)).prod hR).inter_right
    exact isClosed_iInter fun j => isClosed_le
      (continuous_const.mul ((continuous_apply j).comp continuous_fst))
      ((continuous_apply j).comp continuous_snd)
  have he : liftedSet a R ε = (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      weightedPoint a z.1) '' K := by
    ext u
    constructor
    · rintro ⟨q,hq,p,hp,hqp,rfl⟩
      refine ⟨(q,p), ⟨⟨hq,hp⟩, ?_⟩, rfl⟩
      simp only [mem_iInter, mem_ofPred_eq]
      intro j
      nlinarith [(le_div_iff₀ hε).1 (hqp j)]
    · rintro ⟨⟨q,p⟩,⟨⟨hq,hp⟩,hk⟩,rfl⟩
      refine ⟨q,hq,p,hp,?_,rfl⟩
      intro j
      have hj := mem_iInter.mp hk j
      change ε * q j ≤ p j at hj
      exact (le_div_iff₀ hε).2 (by nlinarith)
  rw [he]
  exact hK.image ((weightedPoint_continuous a).comp continuous_fst)

end DiscreteROProof


namespace DiscreteROProof
open Finset

noncomputable def tailMass {n : ℕ} (p z : Fin n → ℝ) (c : ℝ) : ℝ :=
  ∑ i, if c < z i then p i else 0

noncomputable def tailWeights {n : ℕ} (p z : Fin n → ℝ) (c : ℝ) : Fin n → ℝ :=
  fun i => if c < z i then p i / tailMass p z c else 0

lemma tailMass_nonneg {n : ℕ} {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n))
    (z : Fin n → ℝ) (c : ℝ) : 0 ≤ tailMass p z c := by
  exact sum_nonneg fun i _ => by split_ifs <;> simp_all [hp.1]

lemma tailWeights_simplex {n : ℕ} {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n))
    (z : Fin n → ℝ) (c : ℝ) (hm : 0 < tailMass p z c) :
    tailWeights p z c ∈ stdSimplex ℝ (Fin n) := by
  constructor
  · intro i
    dsimp [tailWeights]
    split_ifs
    · exact div_nonneg (hp.1 i) hm.le
    · exact le_rfl
  · have he : (∑ i, tailWeights p z c i) = tailMass p z c / tailMass p z c := by
      change _ = (∑ i, if c < z i then p i else 0) / tailMass p z c
      rw [sum_div]
      apply sum_congr rfl
      intro i _
      simp only [tailWeights, tailMass]
      split_ifs <;> simp
    rw [he, div_self hm.ne']

lemma tailWeights_le {n : ℕ} {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n))
    (z : Fin n → ℝ) (c : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hm : ε < tailMass p z c) (i : Fin n) : tailWeights p z c i ≤ p i / ε := by
  dsimp [tailWeights]
  split_ifs
  · exact div_le_div_of_nonneg_left (hp.1 i) hε hm.le
  · exact div_nonneg (hp.1 i) hε.le

lemma tailWeights_value_gt {n : ℕ} {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n))
    (z : Fin n → ℝ) (c : ℝ) (hm : 0 < tailMass p z c) :
    c < ∑ i, tailWeights p z c i * z i := by
  have hq := tailWeights_simplex hp z c hm
  have he : ∃ i, 0 < tailWeights p z c i := by
    by_contra hh
    push Not at hh
    have hz : ∀ i, tailWeights p z c i = 0 := fun i => le_antisymm (hh i) (hq.1 i)
    have hs := hq.2
    simp only [hz, sum_const_zero] at hs
    norm_num at hs
  obtain ⟨i, hi⟩ := he
  have hz : ∀ j, 0 ≤ tailWeights p z c j * (z j - c) := by
    intro j
    dsimp [tailWeights]
    split_ifs with hj
    · exact mul_nonneg (div_nonneg (hp.1 j) hm.le) (sub_nonneg.mpr hj.le)
    · simp
  have hzi : c < z i := by
    by_contra hh
    simp [tailWeights, hh] at hi
  have hs : 0 < ∑ j, tailWeights p z c j * (z j - c) :=
    sum_pos' (fun j _ => hz j) ⟨i, mem_univ i, mul_pos hi (sub_pos.mpr hzi)⟩
  simp_rw [mul_sub] at hs
  rw [sum_sub_distrib, ← sum_mul, hq.2, one_mul] at hs
  linarith

lemma lowerMass_add_tail {n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ stdSimplex ℝ (Fin n)) (z : Fin n → ℝ) (c : ℝ) :
    (∑ i, if z i ≤ c then p i else 0) + tailMass p z c = 1 := by
  rw [tailMass, ← sum_add_distrib, ← hp.2]
  apply sum_congr rfl
  intro i _
  by_cases hi : z i ≤ c
  · simp [hi, not_lt.mpr hi]
  · simp [hi, lt_of_not_ge hi]

end DiscreteROProof


namespace DiscreteROProof
open MeasureTheory Set Finset
open DataDrivenRO.Discrete

lemma pointLaw_apply {d n : ℕ} (a : Fin n → (Fin d → ℝ))
    {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n))
    {S : Set (Fin d → ℝ)} [DecidablePred (fun u => u ∈ S)] (hS : MeasurableSet S) :
    pointLaw a p S = ENNReal.ofReal (∑ j, if a j ∈ S then p j else 0) := by
  classical
  simp only [pointLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    smul_eq_mul, Measure.dirac_apply' _ hS]
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => by split_ifs <;> simp_all [hp.1])]
  apply sum_congr rfl
  intro j _
  by_cases hj : a j ∈ S <;> simp [hj]

lemma pointLaw_halfspace {d n : ℕ} (a : Fin n → (Fin d → ℝ))
    {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n)) (v : Fin d → ℝ) (c : ℝ) :
    pointLaw a p {u | u ⬝ᵥ v ≤ c} =
      ENNReal.ofReal (∑ j, if a j ⬝ᵥ v ≤ c then p j else 0) := by
  apply pointLaw_apply a hp
  exact isClosed_le (by fun_prop) continuous_const |>.measurableSet

lemma var_threshold_bddBelow {d n : ℕ} (a : Fin n → (Fin d → ℝ))
    {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n)) (v : Fin d → ℝ)
    {ε : ℝ} (hε : ε < 1) :
    BddBelow {c : ℝ | ENNReal.ofReal (1-ε) ≤ pointLaw a p {u | u ⬝ᵥ v ≤ c}} := by
  classical
  have hn : Nonempty (Fin n) := by
    by_contra hh
    have : IsEmpty (Fin n) := not_nonempty_iff.mp hh
    have hs := hp.2
    simp at hs
  let : Nonempty (Fin n) := hn
  obtain ⟨i, hi⟩ := Finset.exists_min_image univ (fun i => a i ⬝ᵥ v) univ_nonempty
  refine ⟨a i ⬝ᵥ v, ?_⟩
  intro c hc
  by_contra hh
  have hz : ∀ j, ¬ a j ⬝ᵥ v ≤ c := by
    intro j hj
    have hm := hi.2 j (mem_univ j)
    linarith
  change ENNReal.ofReal (1-ε) ≤ pointLaw a p {u | u ⬝ᵥ v ≤ c} at hc
  rw [pointLaw_halfspace a hp v c] at hc
  simp only [hz, ite_false, sum_const_zero, ENNReal.ofReal_zero, nonpos_iff_eq_zero,
    ENNReal.ofReal_eq_zero] at hc
  linarith

lemma var_le_threshold {d n : ℕ} (a : Fin n → (Fin d → ℝ))
    {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n)) (v : Fin d → ℝ)
    {ε c : ℝ} (hε : ε < 1)
    (hc : ENNReal.ofReal (1-ε) ≤ pointLaw a p {u | u ⬝ᵥ v ≤ c}) :
    VaR a p ε v ≤ c := by
  exact csInf_le (var_threshold_bddBelow a hp v hε) hc

end DiscreteROProof


namespace DiscreteROProof
open Set Finset MeasureTheory
open DataDrivenRO.Discrete

lemma weightedPoint_dot {d n : ℕ} (a : Fin n → (Fin d → ℝ))
    (q : Fin n → ℝ) (v : Fin d → ℝ) :
    weightedPoint a q ⬝ᵥ v = ∑ i, q i * (a i ⬝ᵥ v) := by
  simp only [weightedPoint, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [sum_mul, mul_assoc]
  rw [sum_comm]
  simp_rw [mul_sum]

lemma support_value_bound {d n : ℕ} (a : Fin n → (Fin d → ℝ))
    {R : Set (Fin n → ℝ)} (hR : IsCompact R) {ε : ℝ} (hε : 0 < ε)
    {p q : Fin n → ℝ} (hp : p ∈ R) (hq : q ∈ stdSimplex ℝ (Fin n))
    (hqp : ∀ j, q j ≤ p j / ε) (v : Fin d → ℝ) :
    ∑ j, q j * (a j ⬝ᵥ v) ≤ RobustMDP.Shared.supportFunction (liftedSet a R ε) v := by
  have hc := (liftedSet_compact a hR hε).image
    (show Continuous (fun u : Fin d → ℝ => u ⬝ᵥ v) by fun_prop)
  rw [← weightedPoint_dot]
  apply le_csSup hc.bddAbove
  exact ⟨weightedPoint a q, ⟨q,hq,p,hp,hqp,rfl⟩,rfl⟩

lemma liftedSet_var_bound {d n : ℕ} (a : Fin n → (Fin d → ℝ))
    {R : Set (Fin n → ℝ)} (hR : IsCompact R) (hsub : R ⊆ stdSimplex ℝ (Fin n))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {p : Fin n → ℝ} (hp : p ∈ R)
    (v : Fin d → ℝ) :
    VaR a p ε v ≤ RobustMDP.Shared.supportFunction (liftedSet a R ε) v := by
  let c := RobustMDP.Shared.supportFunction (liftedSet a R ε) v
  let z : Fin n → ℝ := fun j => a j ⬝ᵥ v
  have hp' := hsub hp
  have hm : tailMass p z c ≤ ε := by
    by_contra hh
    have ht : ε < tailMass p z c := lt_of_not_ge hh
    have ht0 := hε.trans ht
    have hq := tailWeights_simplex hp' z c ht0
    have hv := support_value_bound a hR hε hp hq (tailWeights_le hp' z c hε ht) v
    have hv' := tailWeights_value_gt hp' z c ht0
    change (∑ j, tailWeights p z c j * z j) ≤ c at hv
    linarith
  apply var_le_threshold a hp' v hε1
  rw [pointLaw_halfspace a hp' v c]
  apply ENNReal.ofReal_le_ofReal
  have hs := lowerMass_add_tail hp' z c
  change (∑ j, if a j ⬝ᵥ v ≤ c then p j else 0) + tailMass p z c = 1 at hs
  linarith

end DiscreteROProof


namespace DiscreteROProof
open DataDrivenRO.Discrete

/-- Deterministic content of Theorem 4, p. 13: for every tail level, both uncertainty sets
bound the Value at Risk of each law in the corresponding confidence region.  Their geometric
properties make the real support functions genuine and allow Theorem 1(a) to apply. -/
theorem full_native_result {d n : ℕ} (a : Fin n → (Fin d → ℝ))
    (phat : Fin n → ℝ) (hphat : phat ∈ stdSimplex ℝ (Fin n))
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      (∀ p ∈ chi2Region phat ρ, ∀ v : Fin d → ℝ,
        VaR a p ε v ≤ RobustMDP.Shared.supportFunction (Uchi2 a phat ρ ε) v) ∧
      (∀ p ∈ gRegion phat ρ, ∀ v : Fin d → ℝ,
        VaR a p ε v ≤ RobustMDP.Shared.supportFunction (UG a phat ρ ε) v) ∧
      (Uchi2 a phat ρ ε).Nonempty ∧ Convex ℝ (Uchi2 a phat ρ ε) ∧
        IsCompact (Uchi2 a phat ρ ε) ∧
      (UG a phat ρ ε).Nonempty ∧ Convex ℝ (UG a phat ρ ε) ∧
        IsCompact (UG a phat ρ ε)  := by
  intro ε hε hε1
  obtain ⟨hcn, hcv, hcc⟩ := chi2_geometry hphat hρ
  obtain ⟨hgn, hgv, hgc⟩ := g_geometry hphat hρ
  have hcs : chi2Region phat ρ ⊆ stdSimplex ℝ (Fin n) := fun _ hp => hp.1
  have hgs : gRegion phat ρ ⊆ stdSimplex ℝ (Fin n) := fun _ hp => hp.1
  exact ⟨fun p hp v => liftedSet_var_bound a hcc hcs hε hε1 hp v,
    fun p hp v => liftedSet_var_bound a hgc hgs hε hε1 hp v,
    liftedSet_nonempty a hcn hcs hε hε1.le, liftedSet_convex a hcv hε,
    liftedSet_compact a hcc hε, liftedSet_nonempty a hgn hgs hε hε1.le,
    liftedSet_convex a hgv hε, liftedSet_compact a hgc hε⟩

end DiscreteROProof


open DataDrivenRO.Discrete

namespace DataDrivenRO.Discrete

/-- Deterministic content of Theorem 4, p. 13: for every tail level, both uncertainty sets
bound the Value at Risk of each law in the corresponding confidence region.  Their geometric
properties make the real support functions genuine and allow Theorem 1(a) to apply. -/
theorem theorem_4 {d n : ℕ} (a : Fin n → (Fin d → ℝ))
    (phat : Fin n → ℝ) (hphat : phat ∈ stdSimplex ℝ (Fin n))
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      (∀ p ∈ chi2Region phat ρ, ∀ v : Fin d → ℝ,
        VaR a p ε v ≤ RobustMDP.Shared.supportFunction (Uchi2 a phat ρ ε) v) ∧
      (∀ p ∈ gRegion phat ρ, ∀ v : Fin d → ℝ,
        VaR a p ε v ≤ RobustMDP.Shared.supportFunction (UG a phat ρ ε) v) ∧
      (Uchi2 a phat ρ ε).Nonempty ∧ Convex ℝ (Uchi2 a phat ρ ε) ∧
        IsCompact (Uchi2 a phat ρ ε) ∧
      (UG a phat ρ ε).Nonempty ∧ Convex ℝ (UG a phat ρ ε) ∧
        IsCompact (UG a phat ρ ε) := by
  exact DiscreteROProof.full_native_result a phat hphat ρ hρ

end DataDrivenRO.Discrete

open DataDrivenRO.Discrete

theorem solution {d n : ℕ} (a : Fin n → (Fin d → ℝ))
    (phat : Fin n → ℝ) (hphat : phat ∈ stdSimplex ℝ (Fin n))
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      (∀ p ∈ chi2Region phat ρ, ∀ v : Fin d → ℝ,
        VaR a p ε v ≤ RobustMDP.Shared.supportFunction (Uchi2 a phat ρ ε) v) ∧
      (∀ p ∈ gRegion phat ρ, ∀ v : Fin d → ℝ,
        VaR a p ε v ≤ RobustMDP.Shared.supportFunction (UG a phat ρ ε) v) ∧
      (Uchi2 a phat ρ ε).Nonempty ∧ Convex ℝ (Uchi2 a phat ρ ε) ∧
        IsCompact (Uchi2 a phat ρ ε) ∧
      (UG a phat ρ ε).Nonempty ∧ Convex ℝ (UG a phat ρ ε) ∧
        IsCompact (UG a phat ρ ε) := DataDrivenRO.Discrete.theorem_4 a phat hphat ρ hρ
