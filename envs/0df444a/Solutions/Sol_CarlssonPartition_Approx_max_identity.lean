-- Prove2me | solution 1 for CarlssonPartition.Approx.max_identity
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-17T08:48:02.526153+00:00
-- url     : https://prove2.me/submissions/e681cc2e-9ad8-4a76-a322-804c932aca59

import Definitions.Def_CarlssonPartition_Approx_Setting
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace CarlssonPartition.Approx

lemma piece_subset (I : Instance) (Rs : Fin I.m → Set CarlssonPartition.Equitable.Plane)
    (hP : I.IsPartition Rs) (i : Fin I.m) : Rs i ⊆ I.R := by
  rw [← hP.2.2]
  exact Set.subset_iUnion Rs i

lemma integrability (I : Instance) (hI : I.Standing) :
    IntegrableOn I.f I.R ∧
    IntegrableOn (fun x => ‖x - I.x0‖ * I.f x) I.R := by
  obtain ⟨K, hK⟩ := hI.2.2.2.2.1
  exact ⟨hK.continuousOn.integrableOn_compact hI.1,
    ((continuous_id.sub continuous_const).norm.continuousOn.mul hK.continuousOn).integrableOn_compact hI.1⟩

lemma mu2_expand (I : Instance) (hI : I.Standing)
    (S : Set CarlssonPartition.Equitable.Plane) (hS : S ⊆ I.R) :
    I.mu2 S = I.sbar * I.v * (I.q : ℝ) * I.pr S +
      2 * ∫ x in S, ‖x - I.x0‖ * I.f x := by
  obtain ⟨hf, hr⟩ := integrability I hI
  have hf' := hf.mono_set hS
  have hr' := hr.mono_set hS
  unfold Instance.mu2 Instance.pr
  simp_rw [add_mul, mul_assoc (2 : ℝ)]
  rw [integral_add (hf'.const_mul _) (hr'.const_mul _), integral_const_mul,
    integral_const_mul]

lemma district_leading_core (I : Instance) (hI : I.Standing)
    (S : Set CarlssonPartition.Equitable.Plane) (hS : S ⊆ I.R)
    (hpr : 0 < I.pr S) (lam : ℝ) :
    I.bvrLeading 1 (I.lamSub lam S) S (I.fSub S) =
      I.beta ^ 2 * lam * (1 - 1 / (I.q : ℝ)) ^ 2 * I.mu1 S ^ 2 /
        (2 * I.v ^ 2 * (1 - lam * I.mu2 S / (I.v * (I.q : ℝ))) ^ 2) := by
  have hv : I.v ≠ 0 := ne_of_gt hI.2.2.2.2.2.2.2.1
  have hq : (I.q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hI.2.2.2.2.2.2.2.2.1)
  have hp := ne_of_gt hpr
  have hs := ne_of_gt (Real.sqrt_pos.2 hpr)
  have hs2 := Real.sq_sqrt hpr.le
  have hint : (∫ x in S, Real.sqrt (I.fSub S x)) = I.mu1 S / Real.sqrt (I.pr S) := by
    simp only [Instance.fSub, Real.sqrt_div' _ hpr.le, integral_div, Instance.mu1]
  have hrint : (∫ x in S, ‖x - I.x0‖ * I.fSub S x) =
      (∫ x in S, ‖x - I.x0‖ * I.f x) / I.pr S := by
    simp only [Instance.fSub, ← mul_div_assoc, integral_div]
  have hw : I.workload 1 (I.lamSub lam S) S (I.fSub S) =
      lam * I.mu2 S / (I.v * (I.q : ℝ)) := by
    rw [Instance.workload, hrint, mu2_expand I hI S hS]
    unfold Instance.lamSub
    push_cast
    field_simp
    <;> ring
  rw [Instance.bvrLeading, hint, hw]
  unfold Instance.lamSub
  push_cast
  rw [div_pow, hs2]
  field_simp
  <;> ring

lemma max_identity_core (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) :
    max (((1 + η) / (1 - η)) ^ 2 - 1)
        (1 - ((1 - η) / (1 + η)) ^ 2) =
      ((1 + η) / (1 - η)) ^ 2 - 1 ∧
    ((1 + η) / (1 - η)) ^ 2 - 1 = 4 * η / (1 - η) ^ 2 := by
  have hm : 0 < 1 - η := by linarith
  have hp : 0 < 1 + η := by linarith
  have heq : ((1 + η) / (1 - η)) ^ 2 - 1 = 4 * η / (1 - η) ^ 2 := by
    field_simp
    <;> ring
  have heq' : 1 - ((1 - η) / (1 + η)) ^ 2 = 4 * η / (1 + η) ^ 2 := by
    field_simp
    <;> ring
  refine ⟨max_eq_left ?_, heq⟩
  rw [heq, heq']
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)

lemma density_nonneg_ae (I : Instance) (hI : I.Standing)
    (S : Set CarlssonPartition.Equitable.Plane) (hS : S ⊆ I.R) :
    0 ≤ᵐ[volume.restrict S] I.f := by
  exact ae_restrict_of_ae_restrict_of_subset hS
    (ae_restrict_of_forall_mem hI.1.measurableSet hI.2.2.2.1)

lemma mu1_positive (I : Instance) (hI : I.Standing)
    (S : Set CarlssonPartition.Equitable.Plane) (hS : S ⊆ I.R)
    (hp : 0 < I.pr S) : 0 < I.mu1 S := by
  have hn : 0 ≤ I.mu1 S := integral_nonneg (fun x => Real.sqrt_nonneg _)
  by_contra h
  have hz : I.mu1 S = 0 := le_antisymm (not_lt.mp h) hn
  obtain ⟨K, hK⟩ := hI.2.2.2.2.1
  have hi : IntegrableOn (fun x => Real.sqrt (I.f x)) I.R := (Real.continuous_sqrt.comp_continuousOn hK.continuousOn).integrableOn_compact hI.1
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => Real.sqrt_nonneg (I.f x)) (hi.mono_set hS)).1 hz
  have hfzero : I.f =ᵐ[volume.restrict S] 0 := by
    filter_upwards [hae, density_nonneg_ae I hI S hS] with x hx hfx
    have := Real.sq_sqrt hfx
    simpa [hx] using this.symm
  have : I.pr S = 0 := by
    unfold Instance.pr
    rw [integral_congr_ae hfzero]; simp
  linarith

lemma pr_positive (I : Instance) (hI : I.Standing)
    (S : Set CarlssonPartition.Equitable.Plane) (hS : S ⊆ I.R)
    (hm : 0 < I.mu1 S) : 0 < I.pr S := by
  have hae := density_nonneg_ae I hI S hS
  have hn : 0 ≤ I.pr S := integral_nonneg_of_ae hae
  by_contra h
  have hz : I.pr S = 0 := le_antisymm (not_lt.mp h) hn
  have hfzero := (integral_eq_zero_iff_of_nonneg_ae hae ((integrability I hI).1.mono_set hS)).1 hz
  have hs : (fun x => Real.sqrt (I.f x)) =ᵐ[volume.restrict S] 0 := by
    filter_upwards [hfzero] with x hx
    simp [hx]
  have : I.mu1 S = 0 := by unfold Instance.mu1; rw [integral_congr_ae hs]; simp
  linarith

lemma workload_total (I : Instance) (hI : I.Standing) (lam : ℝ) :
    I.workload I.m lam I.R I.f = lam * I.mu2 I.R / ((I.m : ℝ) * I.v * (I.q : ℝ)) := by
  have hm : (I.m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hI.2.2.2.2.2.2.1)
  have hv : I.v ≠ 0 := ne_of_gt hI.2.2.2.2.2.2.2.1
  have hq : (I.q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hI.2.2.2.2.2.2.2.2.1)
  rw [Instance.workload, mu2_expand I hI I.R (Set.Subset.refl _)]
  have hp : I.pr I.R = 1 := hI.2.2.2.2.2.1
  rw [hp]
  field_simp
  <;> ring

lemma ratio_bounds (a b x y e : ℝ) (ha : 0 < a) (hb : 0 < b)
    (he0 : 0 ≤ e) (he1 : e < 1)
    (hx : |x-a| ≤ e*a) (hy : |y-b| ≤ e*b) :
    (a/b)^2*((1-e)/(1+e))^2 ≤ (x/y)^2 ∧
    (x/y)^2 ≤ (a/b)^2*((1+e)/(1-e))^2 := by
  obtain ⟨hx1,hx2⟩ := abs_le.mp hx
  obtain ⟨hy1,hy2⟩ := abs_le.mp hy
  have hm : 0 < 1-e := by linarith
  have hp : 0 < 1+e := by linarith
  have hxp : 0 ≤ x := by nlinarith [mul_pos ha hm]
  have hyp : 0 < y := by nlinarith [mul_pos hb hm]
  have hl : a*(1-e)/(b*(1+e)) ≤ x/y := by
    apply div_le_div₀ (by positivity) (by nlinarith) hyp (by nlinarith)
  have hu : x/y ≤ a*(1+e)/(b*(1-e)) := by
    apply div_le_div₀ (by positivity) (by nlinarith) (by positivity) (by nlinarith)
  have hl2 := sq_le_sq₀ (by positivity : 0 ≤ a*(1-e)/(b*(1+e))) (by positivity : 0 ≤ x/y) |>.2 hl
  have hu2 := sq_le_sq₀ (by positivity : 0 ≤ x/y) (by positivity : 0 ≤ a*(1+e)/(b*(1-e))) |>.2 hu
  constructor
  · calc
      (a/b)^2*((1-e)/(1+e))^2 = (a*(1-e)/(b*(1+e)))^2 := by rw [mul_div_mul_comm, mul_pow]
      _ ≤ (x/y)^2 := hl2
  · calc
      (x/y)^2 ≤ (a*(1+e)/(b*(1-e)))^2 := hu2
      _ = (a/b)^2*((1+e)/(1-e))^2 := by rw [mul_div_mul_comm, mul_pow]

lemma eta_bounds (a b c ε : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (he : 0 ≤ ε) :
    0 ≤ (min a (b/c))⁻¹*ε ∧
    ε ≤ ((min a (b/c))⁻¹*ε)*a ∧
    c*ε ≤ ((min a (b/c))⁻¹*ε)*b := by
  have hmin : 0 < min a (b/c) := lt_min ha (by positivity)
  have h1 : min a (b/c) ≤ a := min_le_left _ _
  have h2 : c * min a (b/c) ≤ b := by simpa [mul_comm] using (le_div_iff₀ hc).mp (min_le_right a (b/c))
  have heq : ((min a (b/c))⁻¹*ε) * min a (b/c) = ε := by field_simp
  have hnon : 0 ≤ (min a (b/c))⁻¹*ε := by positivity
  refine ⟨hnon, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left h1 hnon]
  · nlinarith [mul_le_mul_of_nonneg_left h2 hnon]

lemma leading_bounds (I : Instance) (hI : I.Standing)
    (Rs : Fin I.m → Set CarlssonPartition.Equitable.Plane) (hP : I.IsPartition Rs)
    (lam ε : ℝ) (hlam : 0 < lam)
    (hstab : I.workload I.m lam I.R I.f < 1) (hε : 0 ≤ ε)
    (h1 : ∀ i, |I.mu1 (Rs i) - (1 / (I.m : ℝ)) * I.mu1 I.R| ≤ ε)
    (h2 : ∀ i, |I.mu2 (Rs i) - (1 / (I.m : ℝ)) * I.mu2 I.R| ≤ ε)
    (hη : I.eta lam ε < 1) :
    0 ≤ I.eta lam ε ∧ 0 ≤ I.bvrLeading I.m lam I.R I.f ∧
    ∀ i,
    I.bvrLeading I.m lam I.R I.f * ((1-I.eta lam ε)/(1+I.eta lam ε))^2 ≤
      I.bvrLeading 1 (I.lamSub lam (Rs i)) (Rs i) (I.fSub (Rs i)) ∧
    I.bvrLeading 1 (I.lamSub lam (Rs i)) (Rs i) (I.fSub (Rs i)) ≤
      I.bvrLeading I.m lam I.R I.f * ((1+I.eta lam ε)/(1-I.eta lam ε))^2 := by
  let a := (1/(I.m:ℝ))*I.mu1 I.R
  let b := 1-lam*I.mu2 I.R/((I.m:ℝ)*I.v*(I.q:ℝ))
  let c := lam/(I.v*(I.q:ℝ))
  let C := I.beta^2*lam*(1-1/(I.q:ℝ))^2/(2*I.v^2)
  have hm : (0:ℝ) < I.m := by exact_mod_cast hI.2.2.2.2.2.2.1
  have hv : 0 < I.v := hI.2.2.2.2.2.2.2.1
  have hq : (0:ℝ) < I.q := by exact_mod_cast hI.2.2.2.2.2.2.2.2.1
  have hpr : I.pr I.R = 1 := hI.2.2.2.2.2.1
  have ha : 0 < a := mul_pos (by positivity) (mu1_positive I hI I.R (Set.Subset.refl _) (by rw [hpr]; norm_num))
  have hb : 0 < b := by dsimp [b]; rw [workload_total I hI] at hstab; linarith
  have hc : 0 < c := by dsimp [c]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbc : b/c = I.v*(I.q:ℝ)/lam*b := by dsimp [c]; field_simp
  have heta : I.eta lam ε = (min a (b/c))⁻¹*ε := by
    change (min a (I.v*(I.q:ℝ)/lam*b))⁻¹*ε = _
    rw [hbc]
  have hbds := eta_bounds a b c ε ha hb hc hε
  rw [← heta] at hbds
  have hT : I.bvrLeading I.m lam I.R I.f = C*(a/b)^2 := by
    rw [Instance.bvrLeading, workload_total I hI]
    change I.beta^2*lam*(1-1/(I.q:ℝ))^2*(I.mu1 I.R)^2 /
      (2*(I.m:ℝ)^2*I.v^2*b^2) = C*(a/b)^2
    dsimp [C,a]
    field_simp
    <;> ring
  refine ⟨hbds.1, ?_, ?_⟩
  · rw [hT]; positivity
  intro i
  have hs := piece_subset I Rs hP i
  have hxi : |I.mu1 (Rs i)-a| ≤ I.eta lam ε*a := (h1 i).trans hbds.2.1
  have hxp : 0 < I.mu1 (Rs i) := by
    have := (abs_le.mp hxi).1
    nlinarith [mul_pos ha (sub_pos.mpr hη)]
  have hpi := pr_positive I hI (Rs i) hs hxp
  have hyi : |(1-c*I.mu2 (Rs i))-b| ≤ I.eta lam ε*b := by
    have hid : (1-c*I.mu2 (Rs i))-b = -c*(I.mu2 (Rs i)-(1/(I.m:ℝ))*I.mu2 I.R) := by
      dsimp [b,c]
      field_simp
      <;> ring
    rw [hid,abs_mul,abs_neg,abs_of_pos hc]
    exact (mul_le_mul_of_nonneg_left (h2 i) hc.le).trans hbds.2.2
  have hr := ratio_bounds a b (I.mu1 (Rs i)) (1-c*I.mu2 (Rs i)) (I.eta lam ε) ha hb hbds.1 hη hxi hyi
  have hTi : I.bvrLeading 1 (I.lamSub lam (Rs i)) (Rs i) (I.fSub (Rs i)) =
      C*(I.mu1 (Rs i)/(1-c*I.mu2 (Rs i)))^2 := by
    rw [district_leading_core I hI (Rs i) hs hpi]
    dsimp [C,c]
    field_simp
    <;> ring
  rw [hT,hTi]
  constructor
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hr.1 hC
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hr.2 hC

lemma proposition_3_core (I : Instance) (hI : I.Standing)
    (Rs : Fin I.m → Set CarlssonPartition.Equitable.Plane) (hP : I.IsPartition Rs)
    (lam ε : ℝ) (hlam : 0 < lam)
    (hstab : I.workload I.m lam I.R I.f < 1) (hε : 0 ≤ ε)
    (h1 : ∀ i, |I.mu1 (Rs i) - (1 / (I.m : ℝ)) * I.mu1 I.R| ≤ ε)
    (h2 : ∀ i, |I.mu2 (Rs i) - (1 / (I.m : ℝ)) * I.mu2 I.R| ≤ ε)
    (hη : I.eta lam ε < 1) :
    ∀ i, |I.bvrLeading 1 (I.lamSub lam (Rs i)) (Rs i) (I.fSub (Rs i)) -
      I.bvrLeading I.m lam I.R I.f| ≤
      4 * I.eta lam ε / (1 - I.eta lam ε) ^ 2 * I.bvrLeading I.m lam I.R I.f := by
  obtain ⟨he, hT, hbds⟩ := leading_bounds I hI Rs hP lam ε hlam hstab hε h1 h2 hη
  obtain ⟨hmax, hfactor⟩ := max_identity_core (I.eta lam ε) he hη
  have hdom := max_eq_left_iff.mp hmax
  have hmul := mul_le_mul_of_nonneg_right hdom hT
  intro i
  have hlo := (hbds i).1
  have hhi := (hbds i).2
  rw [← hfactor]
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
end CarlssonPartition.Approx





open CarlssonPartition.Approx

theorem solution (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) :
    max (((1 + η) / (1 - η)) ^ 2 - 1)
        (1 - ((1 - η) / (1 + η)) ^ 2) =
      ((1 + η) / (1 - η)) ^ 2 - 1 ∧
    ((1 + η) / (1 - η)) ^ 2 - 1 = 4 * η / (1 - η) ^ 2 := by
  exact max_identity_core η hη0 hη1

#print axioms solution
