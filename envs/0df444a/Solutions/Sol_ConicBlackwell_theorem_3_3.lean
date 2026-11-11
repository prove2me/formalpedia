-- Prove2me | solution 1 for ConicBlackwell.theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T14:42:05.923199+00:00
-- url     : https://prove2.me/submissions/1e5a259e-e97f-48eb-b983-8286267a4376

import Definitions.Def_ApproachRegret_ToOLO_AlgorithmOne
import Definitions.Def_PerspEpi_projC
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.Compact
import Definitions.Def_ConicBlackwell_cbaPlusX
import Definitions.Def_ConicBlackwell_weightedRegret
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Positivity
import Definitions.Def_ConicBlackwell_cbaPlusU

-- Inlined component: P045Geometry

set_option autoImplicit false
set_option maxHeartbeats 1000000

open ApproachRegret.ToOLO
open scoped RealInnerProductSpace

namespace S13Geometry

@[simp] theorem lift_head {n : ℕ} (k : ℝ) (x : E n) : lift k x 0 = k := rfl

@[simp] theorem lift_tail {n : ℕ} (k : ℝ) (x : E n) (i : Fin n) :
    lift k x i.succ = x i := rfl

theorem continuous_lift {n : ℕ} (k : ℝ) : Continuous (fun x : E n => lift k x) := by
  unfold lift
  apply (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_const
  · exact PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j

theorem lift_affine {n : ℕ} (k : ℝ) (x y : E n) (a b : ℝ) (hab : a + b = 1) :
    lift k (a • x + b • y) = a • lift k x + b • lift k y := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change k = a * k + b * k
    rw [← add_mul, hab, one_mul]
  · rfl

theorem lift_image_convex {n : ℕ} (k : ℝ) (X : Set (E n)) (hX : Convex ℝ X) :
    Convex ℝ (lift k '' X) := by
  rintro u ⟨x, hx, rfl⟩ v ⟨y, hy, rfl⟩ a b ha hb hab
  exact ⟨a • x + b • y, hX hx hy ha hb hab, lift_affine k x y a b hab⟩

theorem cone_zero {n : ℕ} {K : Set (E n)} (hK : K.Nonempty) : 0 ∈ cone K := by
  obtain ⟨x, hx⟩ := hK
  exact ⟨0, le_rfl, x, hx, (zero_smul ℝ x).symm⟩

theorem cone_smul {n : ℕ} {K : Set (E n)} {u : E n} (hu : u ∈ cone K)
    (a : ℝ) (ha : 0 ≤ a) : a • u ∈ cone K := by
  obtain ⟨b, hb, x, hx, rfl⟩ := hu
  exact ⟨a * b, mul_nonneg ha hb, x, hx, (mul_smul a b x).symm⟩

theorem cone_convex {n : ℕ} {K : Set (E n)} (hK : Convex ℝ K) :
    Convex ℝ (cone K) := by
  rintro u ⟨a, ha, x, hx, rfl⟩ v ⟨b, hb, y, hy, rfl⟩ p q hp hq hpq
  obtain ⟨z, hz, heq⟩ := hK.exists_mem_add_smul_eq hx hy
    (mul_nonneg hp ha) (mul_nonneg hq hb)
  refine ⟨p * a + q * b, add_nonneg (mul_nonneg hp ha) (mul_nonneg hq hb), z, hz, ?_⟩
  simpa only [smul_smul] using heq.symm

/-- A positive first coordinate recovers the scale of every cone point. This
expresses the cone as a closed projection with compact fiber X. -/
theorem lifted_closed {n : ℕ} (k : ℝ) (hk : 0 < k) (X : Set (E n))
    (hX : IsCompact X) : IsClosed (cone (lift k '' X)) := by
  letI : CompactSpace X := isCompact_iff_compactSpace.mp hX
  let S : Set (E (n + 1) × X) :=
    {p | 0 ≤ p.1 0 ∧ p.1 = (p.1 0 / k) • lift k (p.2 : E n)}
  have hcoord : Continuous (fun p : E (n + 1) × X => p.1 0) :=
    (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) 0).comp continuous_fst
  have hbase : Continuous (fun p : E (n + 1) × X => lift k (p.2 : E n)) :=
    (continuous_lift k).comp (continuous_subtype_val.comp continuous_snd)
  have hS : IsClosed S :=
    (isClosed_le continuous_const hcoord).inter
      (isClosed_eq continuous_fst ((hcoord.div_const k).smul hbase))
  have heq : cone (lift k '' X) = Prod.fst '' S := by
    ext u
    constructor
    · rintro ⟨a, ha, z, ⟨x, hx, rfl⟩, hu⟩
      have hu0 : u 0 = a * k := by rw [hu]; rfl
      refine ⟨(u, ⟨x, hx⟩), ?_, rfl⟩
      change 0 ≤ u 0 ∧ u = (u 0 / k) • lift k x
      refine ⟨by rw [hu0]; exact mul_nonneg ha hk.le, ?_⟩
      rw [hu0, mul_div_cancel_right₀ a hk.ne']
      exact hu
    · rintro ⟨⟨u, x⟩, hu, rfl⟩
      exact ⟨u 0 / k, div_nonneg hu.1 hk.le, lift k x,
        ⟨x, x.property, rfl⟩, hu.2⟩
  rw [heq]
  exact isClosedMap_fst_of_compactSpace S hS

section GeneralProjection

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem minimum_eq_iInf {C : Set F} (y p : F) (hp : p ∈ C)
    (hmin : ∀ v ∈ C, ‖y - p‖ ≤ ‖y - v‖) :
    ‖y - p‖ = ⨅ v : C, ‖y - (v : F)‖ := by
  letI : Nonempty C := ⟨⟨p, hp⟩⟩
  apply le_antisymm
  · exact le_ciInf (fun v => hmin v v.property)
  · exact ciInf_le (f := fun v : C => ‖y - (v : F)‖)
      ⟨0, by rintro r ⟨v, rfl⟩; exact norm_nonneg _⟩ ⟨p, hp⟩

theorem projection_unique_exists (C : Set F) (hne : C.Nonempty) (hc : IsClosed C)
    (hcv : Convex ℝ C) (y : F) :
    ∃! p, p ∈ C ∧ ∀ v ∈ C, ‖y - p‖ ≤ ‖y - v‖ := by
  letI : Nonempty C := hne.to_subtype
  obtain ⟨p, hp, heq⟩ := exists_norm_eq_iInf_of_complete_convex hne hc.isComplete hcv y
  have hmin : ∀ v ∈ C, ‖y - p‖ ≤ ‖y - v‖ := by
    intro v hv
    rw [heq]
    exact ciInf_le (f := fun w : C => ‖y - (w : F)‖)
      ⟨0, by rintro r ⟨w, rfl⟩; exact norm_nonneg _⟩ ⟨v, hv⟩
  refine ⟨p, ⟨hp, hmin⟩, ?_⟩
  intro q hq
  have hpq := (norm_eq_iInf_iff_real_inner_le_zero hcv hp).mp heq q hq.1
  have hqp := (norm_eq_iInf_iff_real_inner_le_zero hcv hq.1).mp
    (minimum_eq_iInf y q hq.1 hq.2) p hp
  simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq] at hpq hqp
  have hsym := real_inner_comm p q
  have hnorm := norm_sub_sq_real q p
  have hsq : ‖q - p‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖q - p‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))

theorem projC_minimum (C : Set F) (hne : C.Nonempty) (hc : IsClosed C)
    (hcv : Convex ℝ C) (y : F) :
    PerspEpi.projC C y ∈ C ∧ ∀ v ∈ C, ‖y - PerspEpi.projC C y‖ ≤ ‖y - v‖ := by
  classical
  have hex := projection_unique_exists C hne hc hcv y
  simpa only [PerspEpi.projC, dif_pos hex] using hex.exists.choose_spec

theorem projC_variational (C : Set F) (hne : C.Nonempty) (hc : IsClosed C)
    (hcv : Convex ℝ C) (y : F) :
    ∀ v ∈ C, ⟪y - PerspEpi.projC C y, v - PerspEpi.projC C y⟫ ≤ 0 := by
  have hp := projC_minimum C hne hc hcv y
  exact (norm_eq_iInf_iff_real_inner_le_zero hcv hp.1).mp
    (minimum_eq_iInf y _ hp.1 hp.2)

end GeneralProjection

/-- The exact published projection is the Hilbert projection on the lifted
cone. The residual lies in its negative polar and the projection decreases
the squared norm. -/
theorem projection_properties {n : ℕ} (X : Set (E n)) (hXne : X.Nonempty)
    (hXc : IsCompact X) (hXcv : Convex ℝ X) (hk : 0 < kappa X) (y : E (n + 1)) :
    let C := cone (lift (kappa X) '' X)
    PerspEpi.projC C y ∈ C ∧
      y - PerspEpi.projC C y ∈ polar C ∧
      ‖PerspEpi.projC C y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
  let C := cone (lift (kappa X) '' X)
  let p := PerspEpi.projC C y
  have hzero : 0 ∈ C := cone_zero (hXne.image (lift (kappa X)))
  have hne : C.Nonempty := ⟨0, hzero⟩
  have hc : IsClosed C := lifted_closed (kappa X) hk X hXc
  have hcv : Convex ℝ C := cone_convex (lift_image_convex (kappa X) X hXcv)
  have hp : p ∈ C := (projC_minimum C hne hc hcv y).1
  have hvar : ∀ v ∈ C, ⟪y - p, v - p⟫ ≤ 0 := projC_variational C hne hc hcv y
  have h0 := hvar 0 hzero
  have h2 := hvar ((2 : ℝ) • p) (cone_smul hp 2 (by norm_num))
  have htwice : (2 : ℝ) • p - p = p := by simp [two_smul]
  rw [htwice] at h2
  simp only [zero_sub, inner_neg_right] at h0
  have horth : ⟪y - p, p⟫ = 0 := by linarith
  refine ⟨hp, ?_, ?_⟩
  · intro v hv
    have hv' := hvar v hv
    rw [inner_sub_right, horth, sub_zero] at hv'
    exact hv'
  · have hi : ⟪y, p⟫ = ‖p‖ ^ 2 := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq] at horth
      linarith
    have hn := norm_sub_sq_real y p
    nlinarith [sq_nonneg ‖y - p‖]


end S13Geometry

-- Inlined component: P045Regret

set_option autoImplicit false

open scoped RealInnerProductSpace
open ApproachRegret.ToOLO ConicBlackwell

namespace S13Regret

lemma norm_le_kappa {n : ℕ} (X : Set (E n)) (hXc : IsCompact X)
    (x : E n) (hx : x ∈ X) : ‖x‖ ≤ kappa X := by
  exact le_csSup (hXc.bddAbove_image continuous_norm.continuousOn) ⟨x, hx, rfl⟩

lemma kappa_nonneg {n : ℕ} (X : Set (E n)) (hXne : X.Nonempty)
    (hXc : IsCompact X) : 0 ≤ kappa X := by
  obtain ⟨x, hx⟩ := hXne
  exact (norm_nonneg x).trans (norm_le_kappa X hXc x hx)

lemma eq_zero_of_kappa_zero {n : ℕ} (X : Set (E n)) (hXc : IsCompact X)
    (hk : kappa X = 0) (x : E n) (hx : x ∈ X) : x = 0 := by
  apply norm_eq_zero.mp
  exact le_antisymm (by simpa [hk] using norm_le_kappa X hXc x hx) (norm_nonneg x)

lemma set_eq_singleton_of_kappa_zero {n : ℕ} (X : Set (E n)) (hXne : X.Nonempty)
    (hXc : IsCompact X) (hk : kappa X = 0) : X = {0} := by
  ext x
  constructor
  · intro hx
    exact Set.mem_singleton_iff.mpr (eq_zero_of_kappa_zero X hXc hk x hx)
  · intro hx
    have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
    obtain ⟨y, hy⟩ := hXne
    have hy0 := eq_zero_of_kappa_zero X hXc hk y hy
    simpa [hx0, hy0] using hy

lemma inner_lift {n : ℕ} (a b : ℝ) (x y : E n) :
    ⟪lift a x, lift b y⟫ = a * b + ⟪x, y⟫ := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, lift, dotProduct, Fin.sum_univ_succ,
    mul_comm]

lemma norm_lift_sq {n : ℕ} (a : ℝ) (x : E n) :
    ‖lift a x‖ ^ 2 = a ^ 2 + ‖x‖ ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, lift, Fin.sum_univ_succ]

lemma norm_lift_sq_le {n : ℕ} (X : Set (E n)) (hXc : IsCompact X)
    (x : E n) (hx : x ∈ X) : ‖lift (kappa X) x‖ ^ 2 ≤ 2 * kappa X ^ 2 := by
  have hxk := norm_le_kappa X hXc x hx
  have hk : 0 ≤ kappa X := (norm_nonneg x).trans hxk
  have hs := (sq_le_sq₀ (norm_nonneg x) hk).2 hxk
  rw [norm_lift_sq]
  linarith

lemma lift_mem_cone {n : ℕ} (X : Set (E n)) (x : E n) (hx : x ∈ X) :
    lift (kappa X) x ∈ cone (lift (kappa X) '' X) := by
  exact ⟨1, zero_le_one, lift (kappa X) x, ⟨x, hx, rfl⟩, by simp⟩

lemma chooseDecision_mem {n : ℕ} (X : Set (E n)) (x₀ : E n) (hx₀ : x₀ ∈ X)
    (u : E (n + 1)) (hu : u ∈ cone (lift (kappa X) '' X)) :
    chooseDecision X x₀ u ∈ X := by
  obtain ⟨α, hα, z, ⟨x, hx, rfl⟩, rfl⟩ := hu
  unfold chooseDecision
  split_ifs with hz
  · exact hx₀
  · have hprod : α * kappa X ≠ 0 := by simpa [lift] using hz
    have ha : α ≠ 0 := left_ne_zero_of_mul hprod
    have hk : kappa X ≠ 0 := right_ne_zero_of_mul hprod
    have heq : (kappa X / (α • lift (kappa X) x) 0) •
        tail (α • lift (kappa X) x) = x := by
      ext i
      change (kappa X / (α * kappa X)) * (α * x i) = x i
      field_simp [ha, hk]
      <;> ring
    rw [heq]
    exact hx

lemma payoff_inner_lift {n : ℕ} (X : Set (E n)) (hk : kappa X ≠ 0)
    (x f y : E n) :
    ⟪payoff X x f, lift (kappa X) y⟫ = ⟪f, x⟫ - ⟪f, y⟫ := by
  rw [payoff, inner_lift, div_mul_cancel₀ _ hk, inner_neg_left]
  ring

lemma chooseDecision_smul_lift {n : ℕ} (X : Set (E n)) (x₀ x : E n)
    (α : ℝ) (ha : α ≠ 0) (hk : kappa X ≠ 0) :
    chooseDecision X x₀ (α • lift (kappa X) x) = x := by
  have hh : (α • lift (kappa X) x) 0 ≠ 0 := by
    simpa [lift] using mul_ne_zero ha hk
  rw [chooseDecision, if_neg hh]
  ext i
  change (kappa X / (α * kappa X)) * (α * x i) = x i
  field_simp [ha, hk]
  <;> ring

lemma forcing {n : ℕ} (X : Set (E n)) (hk : 0 < kappa X) (x₀ : E n)
    (u : E (n + 1)) (hu : u ∈ cone (lift (kappa X) '' X)) (f : E n) :
    ⟪u, payoff X (chooseDecision X x₀ u) f⟫ = 0 := by
  obtain ⟨α, hα, z, ⟨x, hx, rfl⟩, rfl⟩ := hu
  by_cases ha : α = 0
  · simp [ha]
  · rw [chooseDecision_smul_lift X x₀ x α ha (ne_of_gt hk), real_inner_smul_left]
    have hz : ⟪lift (kappa X) x, payoff X x f⟫ = 0 := by
      rw [real_inner_comm, payoff_inner_lift X (ne_of_gt hk)]
      exact sub_self _
    rw [hz, mul_zero]

lemma cone_inner_nonneg {n : ℕ} (X : Set (E n)) (hXc : IsCompact X)
    (u z : E (n + 1)) (hu : u ∈ cone (lift (kappa X) '' X))
    (hz : z ∈ cone (lift (kappa X) '' X)) : 0 ≤ ⟪u, z⟫ := by
  obtain ⟨α, hα, v, ⟨x, hx, rfl⟩, rfl⟩ := hu
  obtain ⟨β, hβ, w, ⟨y, hy, rfl⟩, rfl⟩ := hz
  rw [real_inner_smul_left, real_inner_smul_right, inner_lift]
  apply mul_nonneg hα
  apply mul_nonneg hβ
  have hxk := norm_le_kappa X hXc x hx
  have hyk := norm_le_kappa X hXc y hy
  have hk : 0 ≤ kappa X := (norm_nonneg x).trans hxk
  have hprod : ‖x‖ * ‖y‖ ≤ kappa X ^ 2 := by
    simpa only [pow_two] using mul_le_mul hxk hyk (norm_nonneg y) hk
  have hin := (abs_le.mp (abs_real_inner_le_norm x y)).1
  linarith

lemma payoff_norm_sq_le {n : ℕ} (X : Set (E n)) (hXne : X.Nonempty)
    (hXc : IsCompact X) (x f : E n) (hx : x ∈ X) (L : ℝ)
    (hf : ‖f‖ ≤ L) : ‖payoff X x f‖ ^ 2 ≤ 2 * L ^ 2 := by
  have hL : 0 ≤ L := (norm_nonneg f).trans hf
  have hfsq : ‖f‖ ^ 2 ≤ L ^ 2 := (sq_le_sq₀ (norm_nonneg f) hL).2 hf
  rw [payoff, norm_lift_sq, norm_neg]
  by_cases hk : kappa X = 0
  · simp only [hk, div_zero, zero_pow (by decide : 2 ≠ 0), zero_add]
    nlinarith only [hfsq, sq_nonneg L]
  · have hkpos : 0 < kappa X := lt_of_le_of_ne (kappa_nonneg X hXne hXc) (Ne.symm hk)
    have hin : |⟪f, x⟫| ≤ ‖f‖ * kappa X :=
      (abs_real_inner_le_norm f x).trans
        (mul_le_mul_of_nonneg_left (norm_le_kappa X hXc x hx) (norm_nonneg f))
    have hdiv : |⟪f, x⟫ / kappa X| ≤ ‖f‖ := by
      rw [abs_div, abs_of_pos hkpos]
      exact (div_le_iff₀ hkpos).2 hin
    have hs : (⟪f, x⟫ / kappa X) ^ 2 ≤ ‖f‖ ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg (⟪f, x⟫ / kappa X)) (norm_nonneg f)).2 hdiv
    linarith

lemma weighted_payoff_inner {n : ℕ} (X : Set (E n)) (hk : kappa X ≠ 0)
    (θ : ℕ → ℝ) (f play : ℕ → E n) (T : ℕ) (x : E n) :
    ⟪∑ t ∈ Finset.Icc 1 T, θ t • payoff X (play t) (f t), lift (kappa X) x⟫ =
      (∑ t ∈ Finset.Icc 1 T, θ t * ⟪f t, play t⟫) -
        ∑ t ∈ Finset.Icc 1 T, θ t * ⟪f t, x⟫ := by
  rw [sum_inner]
  simp_rw [real_inner_smul_left, payoff_inner_lift X hk, mul_sub]
  rw [Finset.sum_sub_distrib]

lemma weightedRegret_le_of_inner_bound {n : ℕ} (X : Set (E n))
    (hXne : X.Nonempty) (hk : 0 < kappa X) (θ : ℕ → ℝ)
    (f play : ℕ → E n) (T : ℕ) (R : ℝ)
    (hbound : ∀ x ∈ X,
      ⟪∑ t ∈ Finset.Icc 1 T, θ t • payoff X (play t) (f t), lift (kappa X) x⟫ ≤ R) :
    weightedRegret X θ f play T ≤ R := by
  let A := ∑ t ∈ Finset.Icc 1 T, θ t * ⟪f t, play t⟫
  let g := fun x : E n => ∑ t ∈ Finset.Icc 1 T, θ t * ⟪f t, x⟫
  have hcomp (x : E n) (hx : x ∈ X) : A - g x ≤ R := by
    have h := hbound x hx
    rw [weighted_payoff_inner X (ne_of_gt hk)] at h
    exact h
  have hInf : A - R ≤ sInf (g '' X) := by
    apply le_csInf (hXne.image g)
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have h := hcomp x hx
    linarith
  unfold weightedRegret ApproachRegret.Calibration.linRegret
  simp only [real_inner_smul_left]
  change A - sInf (g '' X) ≤ R
  linarith

lemma chooseDecision_zero {n : ℕ} (X : Set (E n)) (hk : kappa X = 0)
    (x₀ : E n) (hx₀ : x₀ = 0) (u : E (n + 1)) : chooseDecision X x₀ u = 0 := by
  simp [chooseDecision, hk, hx₀]

lemma cbaPlusX_zero {n : ℕ} (X : Set (E n)) (hXc : IsCompact X)
    (hk : kappa X = 0) (x₀ x₁ : E n) (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∈ X)
    (ω : ℕ → ℝ) (f : ℕ → E n) (t : ℕ) : cbaPlusX X x₀ x₁ ω f t = 0 := by
  have h0 := eq_zero_of_kappa_zero X hXc hk x₀ hx₀
  have h1 := eq_zero_of_kappa_zero X hXc hk x₁ hx₁
  unfold cbaPlusX
  cases h : t - 1 with
  | zero => simp [h, cbaPlusState, h1]
  | succ k =>
      simp only [h, cbaPlusState]
      exact chooseDecision_zero X hk x₀ h0 _

lemma regret_zero_of_kappa_zero {n : ℕ} (X : Set (E n)) (hXne : X.Nonempty)
    (hXc : IsCompact X) (hk : kappa X = 0) (x₀ x₁ : E n)
    (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∈ X) (ω θ : ℕ → ℝ) (f : ℕ → E n) (T : ℕ) :
    weightedRegret X θ f (cbaPlusX X x₀ x₁ ω f) T = 0 := by
  have hp : cbaPlusX X x₀ x₁ ω f = fun _ => 0 := by
    funext t
    exact cbaPlusX_zero X hXc hk x₀ x₁ hx₀ hx₁ ω f t
  have hset := set_eq_singleton_of_kappa_zero X hXne hXc hk
  rw [hp]
  simp [weightedRegret, ApproachRegret.Calibration.linRegret, hset]

end S13Regret


-- Inlined component: P045Potential

set_option autoImplicit false

open scoped RealInnerProductSpace BigOperators

namespace S13Potential

/-- The hypothesis on successive weight ratios is exactly monotonicity of theta/omega. -/
lemma weight_ratio_mono (ω θ : ℕ → ℝ)
    (hω : ∀ t, 1 ≤ t → 0 < ω t) (hθ : ∀ t, 1 ≤ t → 0 < θ t)
    (hratio : ∀ t, 1 ≤ t → ω (t + 1) / ω t ≤ θ (t + 1) / θ t)
    (t : ℕ) (ht : 1 ≤ t) : θ t / ω t ≤ θ (t + 1) / ω (t + 1) := by
  have h := (div_le_div_iff₀ (hω t ht) (hθ t ht)).mp (hratio t ht)
  apply (div_le_div_iff₀ (hω t ht) (hω (t + 1) (by omega))).mpr
  nlinarith

/-- Weighted telescoping for a nonnegative potential and possibly signed increments. -/
lemma weighted_sum_le (ω θ a b : ℕ → ℝ)
    (hω : ∀ t, 1 ≤ t → 0 < ω t) (hθ : ∀ t, 1 ≤ t → 0 < θ t)
    (hratio : ∀ t, 1 ≤ t → ω (t + 1) / ω t ≤ θ (t + 1) / θ t)
    (ha0 : a 0 = 0) (ha : ∀ t, 0 ≤ a t)
    (hstep : ∀ t, a t + ω (t + 1) * b (t + 1) ≤ a (t + 1)) (T : ℕ) :
    (∑ t ∈ Finset.Icc 1 T, θ t * b t) ≤ (θ T / ω T) * a T := by
  induction T with
  | zero => simp [ha0]
  | succ T ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hα : 0 ≤ θ (T + 1) / ω (T + 1) :=
      le_of_lt (div_pos (hθ _ (by omega)) (hω _ (by omega)))
    have hscaled := mul_le_mul_of_nonneg_left (hstep T) hα
    have hcancel : θ (T + 1) / ω (T + 1) * ω (T + 1) = θ (T + 1) :=
      div_mul_cancel₀ _ (ne_of_gt (hω _ (by omega)))
    rw [mul_add, ← mul_assoc, hcancel] at hscaled
    have hmono : (θ T / ω T) * a T ≤ (θ (T + 1) / ω (T + 1)) * a T := by
      by_cases hT : T = 0
      · simp [hT, ha0]
      · exact mul_le_mul_of_nonneg_right
          (weight_ratio_mono ω θ hω hθ hratio T (by omega)) (ha T)
    linarith

section InnerProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Projection residuals and acuteness transport payoff weights to decision weights. -/
lemma weighted_inner_le (u v : ℕ → H) (ω θ : ℕ → ℝ)
    (hω : ∀ t, 1 ≤ t → 0 < ω t) (hθ : ∀ t, 1 ≤ t → 0 < θ t)
    (hratio : ∀ t, 1 ≤ t → ω (t + 1) / ω t ≤ θ (t + 1) / θ t)
    (hu0 : u 0 = 0) (z : H) (hacute : ∀ t, 0 ≤ ⟪u t, z⟫)
    (hresidual : ∀ t, ⟪u t + ω (t + 1) • v (t + 1) - u (t + 1), z⟫ ≤ 0)
    (T : ℕ) :
    ⟪∑ t ∈ Finset.Icc 1 T, θ t • v t, z⟫ ≤ (θ T / ω T) * ⟪u T, z⟫ := by
  simp only [sum_inner, real_inner_smul_left]
  apply weighted_sum_le ω θ (fun t => ⟪u t, z⟫) (fun t => ⟪v t, z⟫)
      hω hθ hratio (by simp [hu0]) hacute
  intro t
  have h := hresidual t
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left] at h
  linarith

/-- Orthogonality removes the mixed term from every projected update. -/
lemma norm_step (u v : ℕ → H) (ω : ℕ → ℝ)
    (hproj : ∀ t, ‖u (t + 1)‖ ^ 2 ≤ ‖u t + ω (t + 1) • v (t + 1)‖ ^ 2)
    (horth : ∀ t, ⟪u t, v (t + 1)⟫ = 0) (t : ℕ) :
    ‖u (t + 1)‖ ^ 2 ≤ ‖u t‖ ^ 2 + ω (t + 1) ^ 2 * ‖v (t + 1)‖ ^ 2 := by
  have heq : ‖u t + ω (t + 1) • v (t + 1)‖ ^ 2 =
      ‖u t‖ ^ 2 + ω (t + 1) ^ 2 * ‖v (t + 1)‖ ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, horth t]
    simp [norm_smul, Real.norm_eq_abs, mul_pow]
  exact (hproj t).trans_eq heq

/-- The full finite potential bound, including the first projected update. -/
lemma norm_potential (u v : ℕ → H) (ω : ℕ → ℝ) (hu0 : u 0 = 0)
    (hproj : ∀ t, ‖u (t + 1)‖ ^ 2 ≤ ‖u t + ω (t + 1) • v (t + 1)‖ ^ 2)
    (horth : ∀ t, ⟪u t, v (t + 1)⟫ = 0) (T : ℕ) :
    ‖u T‖ ^ 2 ≤ ∑ t ∈ Finset.Icc 1 T, ω t ^ 2 * ‖v t‖ ^ 2 := by
  induction T with
  | zero => simp [hu0]
  | succ T ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hstep := norm_step u v ω hproj horth T
    linarith

lemma norm_sq_bound (u v : ℕ → H) (ω : ℕ → ℝ) (hu0 : u 0 = 0)
    (hproj : ∀ t, ‖u (t + 1)‖ ^ 2 ≤ ‖u t + ω (t + 1) • v (t + 1)‖ ^ 2)
    (horth : ∀ t, ⟪u t, v (t + 1)⟫ = 0) (L : ℝ) (T : ℕ)
    (hv : ∀ t ∈ Finset.Icc 1 T, ‖v t‖ ^ 2 ≤ 2 * L ^ 2) :
    ‖u T‖ ^ 2 ≤ 2 * L ^ 2 * ∑ t ∈ Finset.Icc 1 T, ω t ^ 2 := by
  calc
    ‖u T‖ ^ 2 ≤ ∑ t ∈ Finset.Icc 1 T, ω t ^ 2 * ‖v t‖ ^ 2 :=
      norm_potential u v ω hu0 hproj horth T
    _ ≤ ∑ t ∈ Finset.Icc 1 T, ω t ^ 2 * (2 * L ^ 2) := by
      exact Finset.sum_le_sum (fun t ht => mul_le_mul_of_nonneg_left (hv t ht) (sq_nonneg _))
    _ = 2 * L ^ 2 * ∑ t ∈ Finset.Icc 1 T, ω t ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      ring

/-- Combining the two squared norm bounds yields the corrected constant exactly. -/
lemma final_inner_bound (s u z : H) (α κ L W : ℝ)
    (hα : 0 ≤ α) (hκ : 0 ≤ κ) (hL : 0 ≤ L) (hW : 0 ≤ W)
    (hs : ⟪s, z⟫ ≤ α * ⟪u, z⟫)
    (hu : ‖u‖ ^ 2 ≤ 2 * L ^ 2 * W) (hz : ‖z‖ ^ 2 ≤ 2 * κ ^ 2) :
    ⟪s, z⟫ ≤ 2 * κ * L * α * Real.sqrt W := by
  have hprod : (‖u‖ * ‖z‖) ^ 2 ≤ (2 * L ^ 2 * W) * (2 * κ ^ 2) := by
    rw [mul_pow]
    exact mul_le_mul hu hz (sq_nonneg _) (by positivity)
  have hsq : (‖u‖ * ‖z‖) ^ 2 ≤ (2 * κ * L * Real.sqrt W) ^ 2 := by
    calc
      (‖u‖ * ‖z‖) ^ 2 ≤ (2 * L ^ 2 * W) * (2 * κ ^ 2) := hprod
      _ = (2 * κ * L * Real.sqrt W) ^ 2 := by
        simp only [mul_pow, Real.sq_sqrt hW]
        ring
  have hn := le_of_sq_le_sq hsq (by positivity : 0 ≤ 2 * κ * L * Real.sqrt W)
  calc
    ⟪s, z⟫ ≤ α * ⟪u, z⟫ := hs
    _ ≤ α * (‖u‖ * ‖z‖) := mul_le_mul_of_nonneg_left (real_inner_le_norm u z) hα
    _ ≤ α * (2 * κ * L * Real.sqrt W) := mul_le_mul_of_nonneg_left hn hα
    _ = 2 * κ * L * α * Real.sqrt W := by ring

end InnerProduct

end S13Potential


-- Inlined component: P045Run

set_option autoImplicit false

open scoped RealInnerProductSpace
open ApproachRegret.ToOLO ConicBlackwell

namespace S13Run

variable {n : ℕ} (X : Set (E n)) (x₀ x₁ : E n) (ω : ℕ → ℝ) (f : ℕ → E n)

lemma u_zero : cbaPlusU X x₀ x₁ ω f 0 = 0 := rfl

lemma u_step (t : ℕ) :
    cbaPlusU X x₀ x₁ ω f (t + 1) =
      PerspEpi.projC (cone (lift (kappa X) '' X))
        (cbaPlusU X x₀ x₁ ω f t +
          ω (t + 1) • payoff X (cbaPlusX X x₀ x₁ ω f (t + 1)) (f (t + 1))) := by
  simp [cbaPlusU, cbaPlusX, cbaPlusState]

lemma x_after_update (t : ℕ) :
    cbaPlusX X x₀ x₁ ω f (t + 2) =
      chooseDecision X x₀ (cbaPlusU X x₀ x₁ ω f (t + 1)) := by
  simp [cbaPlusX, cbaPlusU, cbaPlusState]

lemma u_mem (hXne : X.Nonempty) (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (hk : 0 < kappa X) (t : ℕ) :
    cbaPlusU X x₀ x₁ ω f t ∈ cone (lift (kappa X) '' X) := by
  cases t with
  | zero =>
      rw [u_zero]
      exact S13Geometry.cone_zero (hXne.image (lift (kappa X)))
  | succ t =>
      rw [u_step]
      exact (S13Geometry.projection_properties X hXne hXc hXcv hk _).1

lemma state_decision_mem (hXne : X.Nonempty) (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (hk : 0 < kappa X) (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∈ X) (t : ℕ) :
    (cbaPlusState X x₀ x₁ ω f t).1 ∈ X := by
  cases t with
  | zero => exact hx₁
  | succ t =>
      change chooseDecision X x₀ (cbaPlusU X x₀ x₁ ω f (t + 1)) ∈ X
      exact S13Regret.chooseDecision_mem X x₀ hx₀ _ (u_mem X x₀ x₁ ω f hXne hXc hXcv hk _)

lemma x_mem (hXne : X.Nonempty) (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (hk : 0 < kappa X) (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∈ X) (t : ℕ) :
    cbaPlusX X x₀ x₁ ω f t ∈ X := by
  exact state_decision_mem X x₀ x₁ ω f hXne hXc hXcv hk hx₀ hx₁ (t - 1)

lemma forcing_identity (hXne : X.Nonempty) (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (hk : 0 < kappa X) (t : ℕ) :
    ⟪cbaPlusU X x₀ x₁ ω f t,
      payoff X (cbaPlusX X x₀ x₁ ω f (t + 1)) (f (t + 1))⟫ = 0 := by
  cases t with
  | zero => simp [u_zero]
  | succ t =>
      rw [show t.succ + 1 = t + 2 by omega, x_after_update]
      exact S13Regret.forcing X hk x₀ _ (u_mem X x₀ x₁ ω f hXne hXc hXcv hk _) _

lemma projected_norm_le (hXne : X.Nonempty) (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (hk : 0 < kappa X) (t : ℕ) :
    ‖cbaPlusU X x₀ x₁ ω f (t + 1)‖ ^ 2 ≤
      ‖cbaPlusU X x₀ x₁ ω f t +
        ω (t + 1) • payoff X (cbaPlusX X x₀ x₁ ω f (t + 1)) (f (t + 1))‖ ^ 2 := by
  rw [u_step]
  exact (S13Geometry.projection_properties X hXne hXc hXcv hk _).2.2

lemma residual_inner_le (hXne : X.Nonempty) (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (hk : 0 < kappa X) (z : E (n + 1)) (hz : z ∈ cone (lift (kappa X) '' X)) (t : ℕ) :
    ⟪cbaPlusU X x₀ x₁ ω f t +
        ω (t + 1) • payoff X (cbaPlusX X x₀ x₁ ω f (t + 1)) (f (t + 1)) -
          cbaPlusU X x₀ x₁ ω f (t + 1), z⟫ ≤ 0 := by
  rw [u_step]
  exact (S13Geometry.projection_properties X hXne hXc hXcv hk _).2.1 z hz

end S13Run


-- Inlined component: P045

set_option autoImplicit false

open scoped RealInnerProductSpace
open ApproachRegret.ToOLO ConicBlackwell

/-- The unchanged full Theorem 3.3 target, including the zero-radius case. -/
theorem solution {n : ℕ} (X : Set (E n)) (hXne : X.Nonempty) (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (x₀ x₁ : E n) (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∈ X)
    (ω θ : ℕ → ℝ) (hω : ∀ t, 1 ≤ t → 0 < ω t) (hθ : ∀ t, 1 ≤ t → 0 < θ t)
    (hratio : ∀ t, 1 ≤ t → ω (t + 1) / ω t ≤ θ (t + 1) / θ t)
    (f : ℕ → E n) (L : ℝ) (T : ℕ) (hT : 1 ≤ T) (hf : ∀ t ∈ Finset.Icc 1 T, ‖f t‖ ≤ L) :
    weightedRegret X θ f (cbaPlusX X x₀ x₁ ω f) T / (∑ t ∈ Finset.Icc 1 T, θ t) ≤
      2 * kappa X * L * (θ T / ω T) * Real.sqrt (∑ t ∈ Finset.Icc 1 T, ω t ^ 2) /
        (∑ t ∈ Finset.Icc 1 T, θ t) := by
  by_cases hk0 : kappa X = 0
  · rw [S13Regret.regret_zero_of_kappa_zero X hXne hXc hk0 x₀ x₁ hx₀ hx₁ ω θ f T]
    simp [hk0]
  have hk : 0 < kappa X :=
    lt_of_le_of_ne (S13Regret.kappa_nonneg X hXne hXc) (Ne.symm hk0)
  let u := cbaPlusU X x₀ x₁ ω f
  let play := cbaPlusX X x₀ x₁ ω f
  let v := fun t => payoff X (play t) (f t)
  let W := ∑ t ∈ Finset.Icc 1 T, ω t ^ 2
  let α := θ T / ω T
  let R := 2 * kappa X * L * α * Real.sqrt W
  have hL : 0 ≤ L :=
    (norm_nonneg (f 1)).trans (hf 1 (Finset.mem_Icc.mpr ⟨le_rfl, hT⟩))
  have hW : 0 ≤ W := Finset.sum_nonneg (fun t _ => sq_nonneg (ω t))
  have hα : 0 ≤ α := le_of_lt (div_pos (hθ T hT) (hω T hT))
  have hu0 : u 0 = 0 := S13Run.u_zero X x₀ x₁ ω f
  have hu_mem (t : ℕ) : u t ∈ cone (lift (kappa X) '' X) :=
    S13Run.u_mem X x₀ x₁ ω f hXne hXc hXcv hk t
  have hplay (t : ℕ) : play t ∈ X :=
    S13Run.x_mem X x₀ x₁ ω f hXne hXc hXcv hk hx₀ hx₁ t
  have horth (t : ℕ) : ⟪u t, v (t + 1)⟫ = 0 :=
    S13Run.forcing_identity X x₀ x₁ ω f hXne hXc hXcv hk t
  have hproj (t : ℕ) : ‖u (t + 1)‖ ^ 2 ≤ ‖u t + ω (t + 1) • v (t + 1)‖ ^ 2 :=
    S13Run.projected_norm_le X x₀ x₁ ω f hXne hXc hXcv hk t
  have hv (t : ℕ) (ht : t ∈ Finset.Icc 1 T) : ‖v t‖ ^ 2 ≤ 2 * L ^ 2 :=
    S13Regret.payoff_norm_sq_le X hXne hXc (play t) (f t) (hplay t) L (hf t ht)
  have hu_norm : ‖u T‖ ^ 2 ≤ 2 * L ^ 2 * W :=
    S13Potential.norm_sq_bound u v ω hu0 hproj horth L T hv
  have hbound (x : E n) (hx : x ∈ X) :
      ⟪∑ t ∈ Finset.Icc 1 T, θ t • v t, lift (kappa X) x⟫ ≤ R := by
    let z := lift (kappa X) x
    have hz : z ∈ cone (lift (kappa X) '' X) := S13Regret.lift_mem_cone X x hx
    have hacute (t : ℕ) : 0 ≤ ⟪u t, z⟫ :=
      S13Regret.cone_inner_nonneg X hXc (u t) z (hu_mem t) hz
    have hresidual (t : ℕ) : ⟪u t + ω (t + 1) • v (t + 1) - u (t + 1), z⟫ ≤ 0 :=
      S13Run.residual_inner_le X x₀ x₁ ω f hXne hXc hXcv hk z hz t
    have hweighted := S13Potential.weighted_inner_le u v ω θ hω hθ hratio hu0 z hacute hresidual T
    exact S13Potential.final_inner_bound _ (u T) z α (kappa X) L W hα hk.le hL hW
      hweighted hu_norm (S13Regret.norm_lift_sq_le X hXc x hx)
  have hregret : weightedRegret X θ f play T ≤ R :=
    S13Regret.weightedRegret_le_of_inner_bound X hXne hk θ f play T R hbound
  have hsum : 0 ≤ ∑ t ∈ Finset.Icc 1 T, θ t :=
    Finset.sum_nonneg (fun t ht => le_of_lt (hθ t (Finset.mem_Icc.mp ht).1))
  exact div_le_div_of_nonneg_right hregret hsum


#print axioms solution
