-- Prove2me | solution 1 for CerednikDrinfeld.Omega.period_eq_one_of_smul_vertex_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/f5d7a8ed-dc5e-5fa7-9bf4-411eeed72373

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_ThetaMer
import Theorems.Thm_CerednikDrinfeld_Omega_theta_mul_theta_eq_theta
import Theorems.Thm_CerednikDrinfeld_Omega_exists_isUnit_coe_eq_thetaMer_apply_smul_eq_period_mul
import Theorems.Thm_CerednikDrinfeld_Omega_eq_zero_of_mem_holOn_affinoid_of_forall_v_sub_lt_imp_eq_zero
import Theorems.Thm_CerednikDrinfeld_Omega_isDomain_holRing
import Theorems.Thm_CerednikDrinfeld_Omega_isDiscrete_of_finite_stabilizer_stdVertex
import Theorems.Thm_CerednikDrinfeld_Omega_thetaMultipliable_of_isDiscrete_of_isExhausted
import Theorems.Thm_CerednikDrinfeld_Omega_finite_setOf_pmoebius_mem_affinoid
import Theorems.Thm_CerednikDrinfeld_Omega_smul_stdVertex_eq_of_mem_affinoid_zero
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_period_eq_one_of_smul_vertex_eq
p2m_attr_erase "simp" "LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq LocalGL2.swapUnit_val"

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega CerednikDrinfeld.Mumford MulAction Polynomial

namespace Law3W4

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
  [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
  {G : Type} [Group G] (ρ : G →* PGL(2, K₀))

omit [IsTopologicalRing K] [T2Space K] in

theorem theta_same {a z₀ z : K} (hz : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z) (hz₀ : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) :
    theta ρ a a z₀ z = 1 := by
  unfold theta
  have : thetaFactor ρ a a z₀ z = fun _ => 1 := by
    funext γ
    unfold thetaFactor crossRatio
    exact div_self (mul_ne_zero (sub_ne_zero.2 (hz γ).symm) (sub_ne_zero.2 (hz₀ γ).symm))
  rw [this, tprod_one]

omit [IsTopologicalRing K] [T2Space K] in

theorem theta_translate {a b : K} (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) (z₀ z : K) (δ : G) :
    theta ρ (pmoebius K₀ (ρ δ) a) (pmoebius K₀ (ρ δ) b) z₀ z = theta ρ a b z₀ z := by
  unfold theta
  conv_rhs => rw [← Equiv.tprod_eq (Equiv.mulRight δ)]
  congr 1
  funext γ
  simp only [Equiv.coe_mulRight, thetaFactor]
  rw [map_mul, pmoebius_mul K₀ ha, pmoebius_mul K₀ hb]

theorem theta_pow
    (hΘ : ∀ x ∈ upperHalfPlane K₀ K, ∀ y ∈ upperHalfPlane K₀ K, ∀ u ∈ upperHalfPlane K₀ K,
      ∀ w ∈ upperHalfPlane K₀ K, ThetaMultipliable ρ x y u w)
    {a z₀ z : K} (ha : a ∈ upperHalfPlane K₀ K) (hz₀Ω : z₀ ∈ upperHalfPlane K₀ K) (hzΩ : z ∈ upperHalfPlane K₀ K)
    (hz : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z) (hz₀ : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (α : G) (k : ℕ) :
    theta ρ a (pmoebius K₀ (ρ α) a) z₀ z ^ k = theta ρ a (pmoebius K₀ (ρ (α ^ k)) a) z₀ z := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero, map_one]
    have : pmoebius K₀ (1 : PGL(2, K₀)) a = a := by simp [pmoebius]
    rw [this, theta_same ρ hz hz₀]
  | succ k ih =>
    have hka : pmoebius K₀ (ρ (α ^ k)) a ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ ha _
    have hk1a : pmoebius K₀ (ρ (α ^ (k + 1))) a ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ ha _

    have gz : ∀ γ : G, pmoebius K₀ (ρ γ) (pmoebius K₀ (ρ (α ^ k)) a) ≠ z := fun γ h =>
      hz (γ * α ^ k) (by rw [map_mul, pmoebius_mul K₀ ha]; exact h)
    have gz₀ : ∀ γ : G, pmoebius K₀ (ρ γ) (pmoebius K₀ (ρ (α ^ k)) a) ≠ z₀ := fun γ h =>
      hz₀ (γ * α ^ k) (by rw [map_mul, pmoebius_mul K₀ ha]; exact h)
    rw [pow_succ, ih, ← theta_mul_theta_eq_theta ρ gz gz₀ (hΘ a ha _ hka z₀ hz₀Ω z hzΩ)
      (hΘ _ hka _ hk1a z₀ hz₀Ω z hzΩ)]
    congr 1

    rw [show pmoebius K₀ (ρ (α ^ (k + 1))) a = pmoebius K₀ (ρ (α ^ k)) (pmoebius K₀ (ρ α) a) by
      rw [pow_succ, map_mul, pmoebius_mul K₀ ha]]
    exact (theta_translate ρ ha (pmoebius_mem_upperHalfPlane K₀ ha (ρ α)) z₀ z (α ^ k)).symm

end Law3W4

namespace Law3W4

theorem exists_reps (R : Type) [CommRing R] (ϖ : R) [Finite (R ⧸ Ideal.span {ϖ})] (k : ℕ) :
    ∃ S : Finset R, ∀ r : R, ∃ s ∈ S, ϖ ^ k ∣ r - s := by
  classical
  induction k with
  | zero => exact ⟨{0}, fun r => ⟨0, Finset.mem_singleton_self 0, by simp⟩⟩
  | succ k ih =>
    obtain ⟨S, hS⟩ := ih
    haveI : Fintype (R ⧸ Ideal.span {ϖ}) := Fintype.ofFinite _
    let S₁ : Finset R := Finset.univ.image (fun q : R ⧸ Ideal.span {ϖ} => Quotient.out q)
    have hS₁ : ∀ r : R, ∃ t ∈ S₁, ϖ ∣ r - t := by
      intro r
      refine ⟨Quotient.out (Ideal.Quotient.mk (Ideal.span {ϖ}) r), Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
      exact (Ideal.Quotient.mk_out _).symm
    refine ⟨(S₁ ×ˢ S).image (fun p => p.1 + ϖ * p.2), fun r => ?_⟩
    obtain ⟨t, ht, hdt⟩ := hS₁ r
    obtain ⟨r', hr'⟩ := hdt
    obtain ⟨s, hs, hds⟩ := hS r'
    refine ⟨t + ϖ * s, Finset.mem_image.2 ⟨(t, s), Finset.mem_product.2 ⟨ht, hs⟩, rfl⟩, ?_⟩
    obtain ⟨u, hu⟩ := hds
    refine ⟨u, ?_⟩
    have : r - (t + ϖ * s) = ϖ * (r' - s) := by rw [← sub_sub, hr']; ring
    rw [this, hu]; ring

theorem hfinK₀
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (ϖ₁ : PseudoUniformizer K₀ K) (n : ℕ) :
    ∃ T : Finset K₀, ∀ b : K₀,
      Valued.v (algebraMap K₀ K b) ≤ (Valued.v (algebraMap K₀ K ϖ₁.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K b - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ₁.ϖ)) ^ n := by
  classical
  have hinjK : Function.Injective (algebraMap K₀ K) := (algebraMap K₀ K).injective
  have hinjR : Function.Injective (algebraMap R K₀) := IsFractionRing.injective R K₀
  set q : Γ₀ := Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) with hq_def
  have hq0 : q ≠ 0 := by
    rw [hq_def, ne_eq, Valuation.zero_iff, map_eq_zero_iff _ hinjK, map_eq_zero_iff _ hinjR]; exact hϖ.ne_zero
  have hq1 : q < 1 := by
    refine lt_of_le_of_ne (hint ϖ) ?_
    intro h1
    apply hϖ.not_isUnit
    have hinv : Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)⁻¹) ≤ 1 := by
      rw [map_inv₀, Valuation.map_inv, ← hq_def, h1, inv_one]
    obtain ⟨a, ha⟩ := hv _ hinv
    have hϖ0 : algebraMap R K₀ ϖ ≠ 0 := fun h => hϖ.ne_zero (hinjR (by rw [h, map_zero]))
    have hmul : a * ϖ = 1 := hinjR (by rw [map_mul, ha, map_one, inv_mul_cancel₀ hϖ0])
    exact ⟨⟨ϖ, a, (mul_comm ϖ a).trans hmul, hmul⟩, rfl⟩
  set q₁ : Γ₀ := Valued.v (algebraMap K₀ K ϖ₁.ϖ) with hq₁_def
  have hq₁0 : q₁ ≠ 0 := ϖ₁.pos.ne'

  obtain ⟨N, hN⟩ := hq (q₁ ^ n) (pow_ne_zero n hq₁0)

  obtain ⟨S, hS⟩ := exists_reps R ϖ (2 * N + 1)
  have hϖK : algebraMap K₀ K (algebraMap R K₀ ϖ) ≠ 0 := (Valuation.ne_zero_iff Valued.v).1 hq0
  have hϖ₀ : algebraMap R K₀ ϖ ≠ 0 := fun h => hϖK (by rw [h, map_zero])
  refine ⟨S.image (fun s => algebraMap R K₀ s * (algebraMap R K₀ ϖ ^ N)⁻¹), fun b hb => ?_⟩

  have hbN : Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ ^ N * b)) ≤ 1 := by
    rw [map_mul, map_pow, Valuation.map_mul, Valuation.map_pow]
    calc q ^ N * Valued.v (algebraMap K₀ K b) ≤ q₁ ^ n * q₁⁻¹ ^ n := mul_le_mul' hN hb
      _ = 1 := by rw [← mul_pow, mul_inv_cancel₀ hq₁0, one_pow]
  obtain ⟨r, hr⟩ := hv _ hbN
  obtain ⟨s, hs, ⟨u, hu⟩⟩ := hS r
  refine ⟨algebraMap R K₀ s * (algebraMap R K₀ ϖ ^ N)⁻¹, Finset.mem_image.2 ⟨s, hs, rfl⟩, ?_⟩
  have hb' : b = algebraMap R K₀ r * (algebraMap R K₀ ϖ ^ N)⁻¹ := by
    rw [hr, mul_comm (algebraMap R K₀ ϖ ^ N) b, mul_assoc, mul_inv_cancel₀ (pow_ne_zero N hϖ₀), mul_one]
  have hdiff : algebraMap K₀ K b - algebraMap K₀ K (algebraMap R K₀ s * (algebraMap R K₀ ϖ ^ N)⁻¹) =
      algebraMap K₀ K (algebraMap R K₀ ϖ) ^ (2 * N + 1) * algebraMap K₀ K (algebraMap R K₀ u) *
        (algebraMap K₀ K (algebraMap R K₀ ϖ) ^ N)⁻¹ := by
    rw [hb', ← map_sub, ← sub_mul, ← map_sub, hu]
    simp only [map_mul, map_pow, map_inv₀]
  rw [hdiff, Valuation.map_mul, Valuation.map_mul, Valuation.map_inv, Valuation.map_pow, Valuation.map_pow, ← hq_def]
  calc q ^ (2 * N + 1) * Valued.v (algebraMap K₀ K (algebraMap R K₀ u)) * (q ^ N)⁻¹
      ≤ q ^ (2 * N + 1) * 1 * (q ^ N)⁻¹ := by
        gcongr
        exact hint u
    _ = q ^ N * q := by
        rw [mul_one, show 2 * N + 1 = N + (N + 1) by ring, pow_add, mul_comm (q ^ N) (q ^ (N + 1)), mul_assoc,
          mul_inv_cancel₀ (pow_ne_zero N hq0), mul_one, pow_succ]
    _ < q ^ N * 1 := by exact mul_lt_mul_of_pos_left hq1 (pow_pos (zero_lt_iff.2 hq0) N)
    _ = q ^ N := mul_one _
    _ ≤ q₁ ^ n := hN

end Law3W4

theorem solution
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (ϖ₁ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ₁)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀))
    [MulAction G (LT.LatticeTree.Vertex R K₀)]
    [CerednikDrinfeld.Mumford.GraphAction G (CerednikDrinfeld.BruhatTits.tree R K₀)]
    (hρ : CerednikDrinfeld.Mumford.ActsThrough (LT.LatticeTree.Vertex R K₀) ρ)
    (hfin : ∀ w : LT.LatticeTree.Vertex R K₀, Finite (MulAction.stabilizer G w))
    (τ : LT.LatticeTree.Vertex R K₀ → ZMod 2) (hτ : ∀ (g : G) (w : LT.LatticeTree.Vertex R K₀), τ (g • w) = τ w)
    (hadj : ∀ u w : LT.LatticeTree.Vertex R K₀, (CerednikDrinfeld.BruhatTits.tree R K₀).Adj u w → τ u ≠ τ w)
    [DecidableEq (CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀))]
    {E : Type} [Fintype E]
    (eE : E ≃ {e : CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀) // τ e.out.fst = 0})
    (g₀ gₐ : GL (Fin 2) K₀) {w₀ wₐ : K} (hw₀ : w₀ ∈ affinoid ϖ₁ 0) (hwₐ : wₐ ∈ affinoid ϖ₁ 0)
    (hsep : τ (g₀ • LT.LatticeTree.stdVertex R K₀) ≠ τ (gₐ • LT.LatticeTree.stdVertex R K₀))
    (α : G) (v₁ : LT.LatticeTree.Vertex R K₀) (hα : α • v₁ = v₁) (β : G) :
    period ρ (pmoebius K₀ (Matrix.ProjGenLinGroup.mk gₐ) wₐ) (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₀) w₀) α β = 1 := by
  classical

  have hinjK : Function.Injective (algebraMap K₀ K) := (algebraMap K₀ K).injective
  have hinjR : Function.Injective (algebraMap R K₀) := IsFractionRing.injective R K₀
  have hΩₐ : wₐ ∈ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ₁ 0 hwₐ
  have hΩ₀ : w₀ ∈ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ₁ 0 hw₀
  set a : K := pmoebius K₀ (Matrix.ProjGenLinGroup.mk gₐ) wₐ with ha_def
  set z₀ : K := pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₀) w₀ with hz₀_def
  have ha : a ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ hΩₐ _
  have hz₀ : z₀ ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ hΩ₀ _

  choose c hc using fun γ : G => Matrix.ProjGenLinGroup.mk_surjective (ρ γ)
  have actv : ∀ (γ : G) (gl : GL (Fin 2) K₀),
      γ • (gl • (LT.LatticeTree.stdVertex R K₀)) = (c γ * gl) • (LT.LatticeTree.stdVertex R K₀) := by
    intro γ gl; rw [hρ γ, ← hc γ, CerednikDrinfeld.BruhatTits.pgl_mk_smul, mul_smul]
  have actp : ∀ (γ : G) (gl : GL (Fin 2) K₀) {x : K}, x ∈ upperHalfPlane K₀ K →
      pmoebius K₀ (ρ γ) (pmoebius K₀ (Matrix.ProjGenLinGroup.mk gl) x) =
        pmoebius K₀ (Matrix.ProjGenLinGroup.mk (c γ * gl)) x := by
    intro γ gl x hx; rw [← hc γ, ← pmoebius_mul K₀ hx, ← map_mul]
  have τc : ∀ (γ : G) (gl : GL (Fin 2) K₀), τ ((c γ * gl) • (LT.LatticeTree.stdVertex R K₀)) = τ (gl • (LT.LatticeTree.stdVertex R K₀)) := by
    intro γ gl; rw [← actv, hτ]
  have hinv : ∀ (p : PGL(2, K₀)) {y : K}, y ∈ upperHalfPlane K₀ K → pmoebius K₀ p⁻¹ (pmoebius K₀ p y) = y := by
    intro p y hy; rw [← pmoebius_mul K₀ hy, inv_mul_cancel]; simp [pmoebius]
  have hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀ := by
    intro γ h
    rw [ha_def, actp γ gₐ hΩₐ] at h
    have e := smul_stdVertex_eq_of_mem_affinoid_zero R K₀ ϖ hϖ K hint hv ϖ₁ (c γ * gₐ) g₀ (x := z₀)
      (by rw [← h, hinv _ hΩₐ]; exact hwₐ) (by rw [hz₀_def, hinv _ hΩ₀]; exact hw₀)
    apply hsep; rw [← e, τc]
  have hst : {γ : G | ρ γ • (LT.LatticeTree.stdVertex R K₀) = (LT.LatticeTree.stdVertex R K₀)}.Finite := by
    haveI : Finite (stabilizer G (LT.LatticeTree.stdVertex R K₀)) := hfin _
    refine (Set.toFinite ((stabilizer G (LT.LatticeTree.stdVertex R K₀) : Subgroup G) : Set G)).subset ?_
    intro γ hγ
    simp only [Set.mem_setOf_eq] at hγ
    show γ ∈ stabilizer G (LT.LatticeTree.stdVertex R K₀)
    rw [mem_stabilizer_iff, hρ γ]; exact hγ
  have hdisc := isDiscrete_of_finite_stabilizer_stdVertex R K₀ ϖ hϖ K hint hv hq ρ hst
  have hΘ : ∀ x ∈ upperHalfPlane K₀ K, ∀ y ∈ upperHalfPlane K₀ K, ∀ u ∈ upperHalfPlane K₀ K,
      ∀ w ∈ upperHalfPlane K₀ K, ThetaMultipliable ρ x y u w :=
    fun x hx y hy u hu w hw => thetaMultipliable_of_isDiscrete_of_isExhausted ϖ₁ hex ρ hdisc hx hy hu hw

  obtain ⟨U, hUunit, -, hUtheta, hUaut⟩ :=
    exists_isUnit_coe_eq_thetaMer_apply_smul_eq_period_mul K₀ K ϖ₁ hex ρ hdisc ha hz₀ hz₀a α

  have hαfin : IsOfFinOrder α := by
    haveI : Finite (stabilizer G v₁) := hfin v₁
    have h1 : IsOfFinOrder (⟨α, hα⟩ : stabilizer G v₁) := isOfFinOrder_of_finite _
    exact (stabilizer G v₁).subtype.isOfFinOrder h1
  set n : ℕ := orderOf α with hn_def
  have hn : 0 < n := hαfin.orderOf_pos
  have hαn : α ^ n = 1 := pow_orderOf_eq_one α

  have hpow : ∀ z : ↥(upperHalfPlane K₀ K), (¬ ∃ γ : G, pmoebius K₀ (ρ γ) a = (z : K)) →
      ((U : ↥(upperHalfPlane K₀ K) → K) z) ^ n = 1 := by
    intro z hz
    have hz' : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ (z : K) := fun γ h => hz ⟨γ, h⟩
    rw [hUtheta z hz, Law3W4.theta_pow ρ hΘ ha hz₀ z.2 hz' hz₀a α n, hαn, map_one]
    have : pmoebius K₀ (1 : PGL(2, K₀)) a = a := by simp [pmoebius]
    rw [this]
    exact Law3W4.theta_same ρ hz' hz₀a

  have hfinK := Law3W4.hfinK₀ R K₀ ϖ hϖ K hint hv hq ϖ₁
  obtain ⟨m₁, hm₁⟩ := exists_mapsTo_affinoid ϖ₁ (Matrix.ProjGenLinGroup.mk gₐ) 0
  obtain ⟨m₃, hm₃⟩ := exists_mapsTo_affinoid ϖ₁ (Matrix.ProjGenLinGroup.mk g₀) 0
  have haff_a : a ∈ affinoid ϖ₁ m₁ := hm₁ hwₐ
  have haff_z₀ : z₀ ∈ affinoid ϖ₁ m₃ := hm₃ hw₀
  have hmono := affinoid_mono ϖ₁
  set W : ↥(holRing ϖ₁) := U ^ n - 1 with hW_def
  have hWval : ∀ z : ↥(upperHalfPlane K₀ K), (W : ↥(upperHalfPlane K₀ K) → K) z =
      ((U : ↥(upperHalfPlane K₀ K) → K) z) ^ n - 1 := by
    intro z; simp [hW_def]
  have hWzero : ∀ N : ℕ, m₁ ≤ N → m₃ ≤ N → ∀ z : ↥(affinoid ϖ₁ N),
      restrictAffinoid ϖ₁ N (W : ↥(upperHalfPlane K₀ K) → K) z = 0 := by
    intro N h1 h3

    have hF := finite_setOf_pmoebius_mem_affinoid ϖ₁ ρ hdisc N (hmono h1 haff_a)
    obtain ⟨cK, hcK, hball⟩ : ∃ cK : K, cK ≠ 0 ∧ ∀ γ : G, pmoebius K₀ (ρ γ) a ∈ affinoid ϖ₁ N →
        Valued.v cK ≤ Valued.v (pmoebius K₀ (ρ γ) a - z₀) := by
      by_cases hne : hF.toFinset.Nonempty
      · obtain ⟨γ₀, hγ₀, hmin⟩ := hF.toFinset.exists_min_image (fun γ => Valued.v (pmoebius K₀ (ρ γ) a - z₀)) hne
        refine ⟨pmoebius K₀ (ρ γ₀) a - z₀, sub_ne_zero.2 (hz₀a γ₀), fun γ hγ => hmin γ ?_⟩
        rw [Set.Finite.mem_toFinset]; exact hγ
      · refine ⟨1, one_ne_zero, fun γ hγ => ?_⟩
        exact absurd ⟨γ, by rw [Set.Finite.mem_toFinset]; exact hγ⟩ hne
    have hId := eq_zero_of_mem_holOn_affinoid_of_forall_v_sub_lt_imp_eq_zero K₀ K ϖ₁ hrk N (hfinK N)
      (g := restrictAffinoid ϖ₁ N (W : ↥(upperHalfPlane K₀ K) → K)) (W.2 N) (hmono h3 haff_z₀) hcK
      (fun z hz => by
        show (W : ↥(upperHalfPlane K₀ K) → K) ⟨z, affinoid_subset_upperHalfPlane ϖ₁ N z.2⟩ = 0
        rw [hWval, hpow _ ?_, sub_self]
        rintro ⟨γ, hγ⟩
        have hmem : pmoebius K₀ (ρ γ) a ∈ affinoid ϖ₁ N := by rw [hγ]; exact z.2
        have := hball γ hmem
        rw [hγ] at this
        exact absurd (hz.trans_le this) (lt_irrefl _))
    intro z; rw [hId]; rfl
  have hWeq : W = 0 := by
    apply Subtype.ext; funext z
    obtain ⟨m, hm⟩ := hex z z.2
    have := hWzero (max (max m₁ m₃) m) (le_trans (le_max_left _ _) (le_max_left _ _))
      (le_trans (le_max_right _ _) (le_max_left _ _)) ⟨z, hmono (le_max_right _ _) hm⟩
    exact this
  have hUn : U ^ n = 1 := by rw [← sub_eq_zero]; exact hWeq

  haveI : IsDomain ↥(holRing ϖ₁) := isDomain_holRing K₀ K ϖ₁ hrk hex hfinK
  obtain ⟨r, hr⟩ : ∃ r : K, U = algebraMap K ↥(holRing ϖ₁) r := by
    set p : K[X] := X ^ n - 1 with hp
    have hsplit := Polynomial.Splits.eq_prod_roots (IsAlgClosed.splits p)
    have hlead : p.leadingCoeff = 1 := by
      rw [hp]; exact (Polynomial.monic_X_pow_sub_C (1 : K) hn.ne').leadingCoeff
    have heval : Polynomial.aeval U p = 0 := by simp [hp, hUn]
    rw [hsplit, hlead, map_one, one_mul, map_multiset_prod, Multiset.map_map] at heval
    have h0mem := Multiset.prod_eq_zero_iff.1 heval
    rw [Multiset.mem_map] at h0mem
    obtain ⟨r, -, hr0⟩ := h0mem
    refine ⟨r, ?_⟩
    simp only [Function.comp_apply, map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at hr0
    exact sub_eq_zero.1 hr0

  have haut := hUaut β ⟨z₀, hz₀⟩
  have hconst : ∀ z : ↥(upperHalfPlane K₀ K), (U : ↥(upperHalfPlane K₀ K) → K) z = r := by
    intro z; rw [hr]; rfl
  rw [hconst, hconst] at haut
  have hr0 : r ≠ 0 := by
    intro h0
    apply hUunit.ne_zero
    rw [hr, h0, map_zero]
  have := mul_right_cancel₀ hr0 (haut.symm.trans (one_mul r).symm)
  simpa [ha_def, hz₀_def] using this

end S_CerednikDrinfeld_Omega_period_eq_one_of_smul_vertex_eq
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_period_eq_one_of_smul_vertex_eq (solution)
