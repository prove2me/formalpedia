-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_points_prod_theta_eq_of_v_sub_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/5cc94d96-d62b-5af0-adc3-61bbae70a46e

import Mathlib
import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Theorems.Thm_CerednikDrinfeld_Omega_exists_isUnit_coe_eq_thetaMer_apply_smul_eq_period_mul
import Theorems.Thm_CerednikDrinfeld_Omega_theta_pmoebius_mul_theta_eq_theta
import Theorems.Thm_CerednikDrinfeld_Omega_theta_apply_pmoebius_basePoint_eq_one_of_isOfFinOrder
import Theorems.Thm_CerednikDrinfeld_Omega_exists_monoidHom_fracAct_thetaMer_eq
import Theorems.Thm_CerednikDrinfeld_Omega_isDiscrete_of_finite_stabilizer_stdVertex
import Theorems.Thm_CerednikDrinfeld_Omega_thetaMultipliable_of_isDiscrete_of_mem_affinoid
import Theorems.Thm_CerednikDrinfeld_Omega_finite_setOf_pmoebius_mem_affinoid
import Theorems.Thm_CerednikDrinfeld_BruhatTits_finite_quotEdge_of_finite_quotVert
import Theorems.Thm_CerednikDrinfeld_Omega_exists_isUnit_det_pathCycle_and_span_pathCycle
import Theorems.Thm_CerednikDrinfeld_Omega_monoidHom_eq_of_forall_isOfFinOrder_of_forall_apply_eq_of_span_pathCycle
import Theorems.Thm_Valued_v_prod_sub_one_sub_sum_sub_le_of_forall_v_sub_sub_mul_sub_le
import Theorems.Thm_Valued_exists_mulVec_add_eq_of_v_det_eq_one
import Theorems.Thm_CerednikDrinfeld_Omega_exists_v_sub_sub_mul_le_mul_sq_of_mem_affinoid_zero
import Theorems.Thm_CerednikDrinfeld_Omega_v_apply_eq_of_mem_holOn_affinoid_zero_of_mul_eq_one
import Theorems.Thm_CerednikDrinfeld_Omega_exists_v_det_eq_one_of_isUnit_det_pathCycle_of_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_points_prod_theta_eq_of_v_sub_one_lt
p2m_attr_erase "simp" "LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq CerednikDrinfeld.Mumford.walkOverlap_nil_right CerednikDrinfeld.Mumford.walkOverlap_nil_left LocalGL2.swapUnit_val"

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega CerednikDrinfeld.Mumford

namespace JC3d

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem apply_ne_zero_of_isUnit (Q : PseudoUniformizer K₀ K) (f : ↥(holRing Q)) (hf : IsUnit f)
    (z : ↥(upperHalfPlane K₀ K)) : (f : ↥(upperHalfPlane K₀ K) → K) z ≠ 0 := by
  intro h0
  obtain ⟨g, hfg⟩ := hf.exists_right_inv
  have := congrArg (fun h : ↥(holRing Q) => (h : ↥(upperHalfPlane K₀ K) → K) z) hfg
  beta_reduce at this
  rw [show ((f * g : ↥(holRing Q)) : ↥(upperHalfPlane K₀ K) → K) z =
    (f : ↥(upperHalfPlane K₀ K) → K) z * (g : ↥(upperHalfPlane K₀ K) → K) z from rfl, h0, zero_mul] at this
  exact zero_ne_one this

theorem add_mem_affinoid_zero (Q : PseudoUniformizer K₀ K) {b e : K} (hb : b ∈ affinoid Q 0) (he : Valued.v e < 1) :
    b + e ∈ affinoid Q 0 := by
  rw [mem_affinoid_iff'] at hb ⊢
  obtain ⟨hb1, hb2⟩ := hb
  simp only [pow_zero] at hb1 hb2 ⊢
  refine ⟨?_, fun a => ?_⟩
  · exact (Valuation.map_add _ _ _).trans (max_le hb1 he.le)
  · have hlt : Valued.v e < Valued.v (b - algebraMap K₀ K a) := lt_of_lt_of_le he (hb2 a)
    rw [show b + e - algebraMap K₀ K a = (b - algebraMap K₀ K a) + e by ring, Valuation.map_add_eq_of_lt_left _ hlt]
    exact hb2 a

theorem add_mem_upperHalfPlane (Q : PseudoUniformizer K₀ K) {b e : K} (hb : b ∈ affinoid Q 0) (he : Valued.v e < 1) :
    b + e ∈ upperHalfPlane K₀ K :=
  affinoid_subset_upperHalfPlane Q 0 (add_mem_affinoid_zero Q hb he)

theorem thetaMultipliable [CompleteSpace K] (Q : PseudoUniformizer K₀ K) (hex : IsExhausted Q)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    {a b z₀ z : K} (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz : z ∈ upperHalfPlane K₀ K) : ThetaMultipliable ρ a b z₀ z := by
  obtain ⟨n₁, h₁⟩ := hex a ha
  obtain ⟨n₂, h₂⟩ := hex b hb
  obtain ⟨n₃, h₃⟩ := hex z₀ hz₀
  obtain ⟨n₄, h₄⟩ := hex z hz
  have e1 : n₁ ≤ max (max n₁ n₂) (max n₃ n₄) := le_trans (le_max_left _ _) (le_max_left _ _)
  have e2 : n₂ ≤ max (max n₁ n₂) (max n₃ n₄) := le_trans (le_max_right _ _) (le_max_left _ _)
  have e3 : n₃ ≤ max (max n₁ n₂) (max n₃ n₄) := le_trans (le_max_left _ _) (le_max_right _ _)
  have e4 : n₄ ≤ max (max n₁ n₂) (max n₃ n₄) := le_trans (le_max_right _ _) (le_max_right _ _)
  exact CerednikDrinfeld.Omega.thetaMultipliable_of_isDiscrete_of_mem_affinoid Q ρ hρ _
    (affinoid_mono Q e1 h₁) (affinoid_mono Q e2 h₂) (affinoid_mono Q e3 h₃) (affinoid_mono Q e4 h₄)

theorem mem_affinoid_of_v_sub_lt (Q : PseudoUniformizer K₀ K) {n : ℕ} {z w : K} (hz : z ∈ affinoid Q n)
    (hw : Valued.v (w - z) < Valued.v (algebraMap K₀ K Q.ϖ) ^ n) : w ∈ affinoid Q n := by
  have hrr : Valued.v (algebraMap K₀ K Q.ϖ) ^ n ≤ (Valued.v (algebraMap K₀ K Q.ϖ))⁻¹ ^ n :=
    (pow_le_one₀ Q.pos.le Q.lt_one.le).trans (one_le_pow₀ ((one_le_inv₀ Q.pos).2 Q.lt_one.le))
  rw [mem_affinoid_iff'] at hz ⊢
  refine ⟨?_, fun x => ?_⟩
  · have : w = z + (w - z) := by ring
    rw [this]
    exact Valuation.map_add_le _ hz.1 (hw.le.trans hrr)
  · have h1 : Valued.v (w - z) < Valued.v (z - algebraMap K₀ K x) := hw.trans_le (hz.2 x)
    have : w - algebraMap K₀ K x = (z - algebraMap K₀ K x) + (w - z) := by ring
    rw [this, Valuation.map_add_eq_of_lt_left _ h1]
    exact hz.2 x

theorem exists_mem_upperHalfPlane_forall_pmoebius_ne
    (Q : PseudoUniformizer K₀ K) (hex : IsExhausted Q)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hdisc : IsDiscrete K ρ)
    {x : K} (hx : x ∈ upperHalfPlane K₀ K) :
    ∃ w : K, w ∈ upperHalfPlane K₀ K ∧ ∀ γ : G, pmoebius K₀ (ρ γ) x ≠ w := by
  classical
  obtain ⟨N, hxN⟩ := hex x hx
  set z : ℕ → K := fun k => x + algebraMap K₀ K Q.ϖ ^ (k + N + 1) with hz
  have hzN : ∀ k, z k ∈ affinoid Q N := fun k => by
    refine mem_affinoid_of_v_sub_lt Q hxN ?_
    rw [hz]; dsimp only
    rw [add_sub_cancel_left, Valuation.map_pow]
    exact pow_lt_pow_right_of_lt_one₀ Q.pos Q.lt_one (by omega)
  have hzinj : Function.Injective z := by
    intro k k' h
    rw [hz] at h
    have h' : Valued.v (algebraMap K₀ K Q.ϖ) ^ (k + N + 1) = Valued.v (algebraMap K₀ K Q.ϖ) ^ (k' + N + 1) := by
      rw [← Valuation.map_pow, ← Valuation.map_pow]; exact congrArg _ (add_left_cancel h)
    have := pow_right_injective₀ Q.pos Q.lt_one.ne h'
    omega
  have hfin : {γ : G | pmoebius K₀ (ρ γ) x ∈ affinoid Q N}.Finite :=
    CerednikDrinfeld.Omega.finite_setOf_pmoebius_mem_affinoid Q ρ hdisc N hxN
  have hbad : {k : ℕ | ∃ γ : G, pmoebius K₀ (ρ γ) x = z k}.Finite := by
    refine Set.Finite.subset ((hfin.image fun γ => pmoebius K₀ (ρ γ) x).preimage (hzinj.injOn)) ?_
    rintro k ⟨γ, h⟩
    exact ⟨γ, by rw [Set.mem_setOf_eq, h]; exact hzN k, h⟩
  obtain ⟨k, -, hk⟩ := Set.Infinite.exists_notMem_finite (Set.infinite_univ (α := ℕ)) hbad
  simp only [Set.mem_setOf_eq, not_exists] at hk
  exact ⟨z k, affinoid_subset_upperHalfPlane Q N (hzN k), fun γ => hk γ⟩

theorem exists_monoidHom_prod_theta [CompleteSpace K] [IsAlgClosed K]
    (Q : PseudoUniformizer K₀ K) (hex : IsExhausted Q) [IsDomain ↥(holRing Q)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hdisc : IsDiscrete K ρ)
    {z₀ : K} (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (n : ℕ) (a b : Fin n → K) (ha : ∀ i, a i ∈ upperHalfPlane K₀ K) (hb : ∀ i, b i ∈ upperHalfPlane K₀ K)
    (hza : ∀ i (γ : G), pmoebius K₀ (ρ γ) (a i) ≠ z₀) (hzb : ∀ i (γ : G), pmoebius K₀ (ρ γ) (b i) ≠ z₀) :
    ∃ c : G →* Kˣ, (∀ β : G, ((c β : Kˣ) : K) = ∏ i, theta ρ (a i) (b i) z₀ (pmoebius K₀ (ρ β) z₀)) ∧
      ∀ γ : G, IsOfFinOrder γ → c γ = 1 := by
  classical
  have hci : ∀ i : Fin n, ∃ c : G →* Kˣ, ∀ β : G, ((c β : Kˣ) : K) = theta ρ (a i) (b i) z₀ (pmoebius K₀ (ρ β) z₀) := by
    intro i
    obtain ⟨c, hc, -⟩ := CerednikDrinfeld.Omega.exists_monoidHom_fracAct_thetaMer_eq K₀ K Q hex ρ hdisc
      (ha i) (hb i) hz₀ (hza i) (hzb i)
    exact ⟨c, hc⟩
  choose c hc using hci
  refine ⟨∏ i, c i, fun β => ?_, fun γ hγ => ?_⟩
  · rw [MonoidHom.finsetProd_apply, Units.coe_prod]
    exact Finset.prod_congr rfl fun i _ => hc i β
  · rw [MonoidHom.finsetProd_apply]
    refine Finset.prod_eq_one fun i _ => ?_
    apply Units.val_eq_one.mp
    rw [hc i γ]
    exact CerednikDrinfeld.Omega.theta_apply_pmoebius_basePoint_eq_one_of_isOfFinOrder K₀ K Q hex ρ hdisc
      (ha i) (hb i) hz₀ (hza i) (hzb i) γ hγ

theorem lipschitz_of_pins (f : K → K) (d : K)
    (h0 : ∀ e : K, Valued.v e < 1 → Valued.v (f e - f 0 - d * e) ≤ Valued.v e ^ 2)
    (hc : ∀ e' : K, Valued.v e' < 1 → ∃ d' : K, ∀ e : K, Valued.v e < 1 →
      Valued.v (f e - f e' - d' * (e - e')) ≤ Valued.v (e - e') ^ 2)
    (e e' : K) (s t : Γ₀) (hs : s < 1) (he : Valued.v e ≤ s) (he' : Valued.v e' ≤ s) (hee' : Valued.v (e - e') ≤ t) :
    Valued.v (f e - f e' - d * (e - e')) ≤ t * s := by
  have hes : Valued.v e < 1 := lt_of_le_of_lt he hs
  have he's : Valued.v e' < 1 := lt_of_le_of_lt he' hs
  by_cases he0 : e' = 0
  · subst he0
    rw [sub_zero] at hee' ⊢
    calc Valued.v (f e - f 0 - d * e) ≤ Valued.v e ^ 2 := h0 e hes
      _ = Valued.v e * Valued.v e := pow_two _
      _ ≤ t * s := mul_le_mul' hee' he
  · obtain ⟨d', hd'⟩ := hc e' he's
    have A := h0 e' he's
    have B := hd' 0 (by rw [map_zero]; exact zero_lt_one)
    have hsum : (f e' - f 0 - d * e') + (f 0 - f e' - d' * (0 - e')) = (d' - d) * e' := by ring
    have hdd : Valued.v (d' - d) ≤ Valued.v e' := by
      have h1 : Valued.v ((d' - d) * e') ≤ Valued.v e' ^ 2 := by
        rw [← hsum]
        refine (Valuation.map_add _ _ _).trans (max_le A ?_)
        have : Valued.v (0 - e') = Valued.v e' := by rw [zero_sub, Valuation.map_neg]
        rw [this] at B
        exact B
      rw [Valuation.map_mul, pow_two] at h1
      have hne : Valued.v e' ≠ 0 := (Valuation.ne_zero_iff _).mpr he0
      have h2 := mul_le_mul_left h1 (Valued.v e')⁻¹
      rwa [mul_assoc, mul_inv_cancel₀ hne, mul_one, mul_assoc, mul_inv_cancel₀ hne, mul_one] at h2
    have hmain : f e - f e' - d * (e - e') = (f e - f e' - d' * (e - e')) + (d' - d) * (e - e') := by ring
    have hee's : Valued.v (e - e') ≤ s := (Valuation.map_sub _ _ _).trans (max_le he he')
    rw [hmain]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
    · refine (hd' e hes).trans ?_
      rw [pow_two]
      exact mul_le_mul' hee' hee's
    · rw [Valuation.map_mul]
      calc Valued.v (d' - d) * Valued.v (e - e') ≤ Valued.v e' * t := mul_le_mul' hdd hee'
        _ ≤ s * t := mul_le_mul' he' le_rfl
        _ = t * s := mul_comm _ _

theorem holPins [CompleteSpace K] [IsAlgClosed K] (Q : PseudoUniformizer K₀ K)
    (U : ↥(holRing Q)) (hU : IsUnit U) (g : GL (Fin 2) K₀) (b : ↥(upperHalfPlane K₀ K)) (hb : (b : K) ∈ affinoid Q 0)
    (e' : K) (he' : Valued.v e' < 1) :
    ∃ d' : K, Valued.v d' ≤ 1 ∧ ∀ (e : K) (he : Valued.v e < 1),
      Valued.v ((U : ↥(upperHalfPlane K₀ K) → K) ((Matrix.ProjGenLinGroup.mk g) • ⟨(b : K) + e, add_mem_upperHalfPlane Q hb he⟩) /
            (U : ↥(upperHalfPlane K₀ K) → K) ((Matrix.ProjGenLinGroup.mk g) • b)
        - (U : ↥(upperHalfPlane K₀ K) → K) ((Matrix.ProjGenLinGroup.mk g) • ⟨(b : K) + e', add_mem_upperHalfPlane Q hb he'⟩) /
            (U : ↥(upperHalfPlane K₀ K) → K) ((Matrix.ProjGenLinGroup.mk g) • b)
        - d' * (e - e')) ≤ Valued.v (e - e') ^ 2 := by

  set F : ↥(holRing Q) := (Matrix.ProjGenLinGroup.mk g)⁻¹ • U with hF
  have hFapp : ∀ z : ↥(upperHalfPlane K₀ K),
      (F : ↥(upperHalfPlane K₀ K) → K) z = (U : ↥(upperHalfPlane K₀ K) → K) ((Matrix.ProjGenLinGroup.mk g) • z) := by
    intro z; rw [hF, coe_smul_holRing_apply, inv_inv]
  have hFu : IsUnit F := hU.map (MulSemiringAction.toRingHom _ ↥(holRing Q) (Matrix.ProjGenLinGroup.mk g)⁻¹)
  obtain ⟨Finv, hFFinv⟩ := hFu.exists_right_inv

  have hconst : ∀ z z' : ↥(upperHalfPlane K₀ K), (z : K) ∈ affinoid Q 0 → (z' : K) ∈ affinoid Q 0 →
      Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) z) = Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) z') := by
    intro z z' hz hz'
    have hmul : restrictAffinoid Q 0 (F : ↥(upperHalfPlane K₀ K) → K) * restrictAffinoid Q 0 (Finv : ↥(upperHalfPlane K₀ K) → K) = 1 := by
      funext x
      have := congrArg (fun h : ↥(holRing Q) => (h : ↥(upperHalfPlane K₀ K) → K)
        (Set.inclusion (affinoid_subset_upperHalfPlane Q 0) x)) hFFinv
      simpa [restrictAffinoid] using this
    exact CerednikDrinfeld.Omega.v_apply_eq_of_mem_holOn_affinoid_zero_of_mul_eq_one Q (F.2 0) (Finv.2 0) hmul ⟨z, hz⟩ ⟨z', hz'⟩
  have hc0 : (F : ↥(upperHalfPlane K₀ K) → K) b ≠ 0 := apply_ne_zero_of_isUnit Q F hFu b
  have hMne : Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) b) ≠ 0 := (Valuation.ne_zero_iff _).mpr hc0
  have hM : ∀ z : ↥(upperHalfPlane K₀ K), (z : K) ∈ affinoid Q 0 →
      Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) z) ≤ Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) b) :=
    fun z hz => (hconst z b hz hb).le

  have hb' : (b : K) + e' ∈ affinoid Q 0 := add_mem_affinoid_zero Q hb he'
  obtain ⟨d₀, hd₀, hpin⟩ := CerednikDrinfeld.Omega.exists_v_sub_sub_mul_le_mul_sq_of_mem_affinoid_zero K₀ K Q F _ hM
    ⟨(b : K) + e', add_mem_upperHalfPlane Q hb he'⟩ hb'
  refine ⟨d₀ / (F : ↥(upperHalfPlane K₀ K) → K) b, ?_, fun e he => ?_⟩
  · rw [map_div₀, div_le_iff₀ (pos_iff_ne_zero.mpr hMne), one_mul]
    exact hd₀
  · set zb : ↥(upperHalfPlane K₀ K) := ⟨(b : K) + e, add_mem_upperHalfPlane Q hb he⟩ with hzb
    set zb' : ↥(upperHalfPlane K₀ K) := ⟨(b : K) + e', add_mem_upperHalfPlane Q hb he'⟩ with hzb'
    have hsub : (zb : K) - (zb' : K) = e - e' := by
      show (b : K) + e - ((b : K) + e') = e - e'
      rw [add_sub_add_left_eq_sub]
    have hz : Valued.v ((zb : K) - (zb' : K)) < 1 := by
      rw [hsub]
      exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt he he')
    have key := hpin zb hz
    rw [hFapp, hFapp, hsub] at key
    rw [← hFapp b, div_mul_eq_mul_div, ← sub_div, ← sub_div, map_div₀, div_le_iff₀ (pos_iff_ne_zero.mpr hMne),
      mul_comm (Valued.v (e - e') ^ 2) _]
    exact key

theorem newtonSolve [CompleteSpace K] [IsAlgClosed K]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (Q : PseudoUniformizer K₀ K)
    {r : ℕ} (U : Fin r → ↥(holRing Q)) (hU : ∀ j, IsUnit (U j))
    (g : Fin r → GL (Fin 2) K₀) (b : Fin r → ↥(upperHalfPlane K₀ K)) (d : Matrix (Fin r) (Fin r) K)
    (hb : ∀ i, ((b i : ↥(upperHalfPlane K₀ K)) : K) ∈ affinoid Q 0)
    (hd : ∀ i j, Valued.v (d i j) ≤ 1) (hdet : Valued.v d.det = 1)
    (hpin : ∀ (i j : Fin r) (z : ↥(upperHalfPlane K₀ K)), Valued.v ((z : K) - (b i : K)) < 1 →
        Valued.v ((U j : ↥(upperHalfPlane K₀ K) → K) ((Matrix.ProjGenLinGroup.mk (g i)) • z)
            - (U j : ↥(upperHalfPlane K₀ K) → K) ((Matrix.ProjGenLinGroup.mk (g i)) • (b i)) * (1 + d i j * ((z : K) - (b i : K))))
          ≤ Valued.v ((U j : ↥(upperHalfPlane K₀ K) → K) ((Matrix.ProjGenLinGroup.mk (g i)) • (b i))) * Valued.v ((z : K) - (b i : K)) ^ 2)
    (y : Fin r → K) (hy : ∀ j, Valued.v (y j - 1) < 1) :
    ∃ (ε : Fin r → K) (hε : ∀ i, (b i : K) + ε i ∈ upperHalfPlane K₀ K),
      (∀ i, Valued.v (ε i) < 1) ∧
      ∀ j, ∏ i, (U j : ↥(upperHalfPlane K₀ K) → K) ((Matrix.ProjGenLinGroup.mk (g i)) • ⟨(b i : K) + ε i, hε i⟩) /
              (U j : ↥(upperHalfPlane K₀ K) → K) ((Matrix.ProjGenLinGroup.mk (g i)) • (b i)) = y j := by
  classical
  have hUne : ∀ (j : Fin r) (x : ↥(upperHalfPlane K₀ K)), (U j : ↥(upperHalfPlane K₀ K) → K) x ≠ 0 :=
    fun j x => apply_ne_zero_of_isUnit Q (U j) (hU j) x

  let F : Fin r → Fin r → K → K := fun i j e =>
    if he : Valued.v e < 1 then
      (U j : ↥(upperHalfPlane K₀ K) → K) ((Matrix.ProjGenLinGroup.mk (g i)) • ⟨(b i : K) + e, add_mem_upperHalfPlane Q (hb i) he⟩) /
        (U j : ↥(upperHalfPlane K₀ K) → K) ((Matrix.ProjGenLinGroup.mk (g i)) • (b i))
    else 1
  have hFdef : ∀ (i j : Fin r) (e : K) (he : Valued.v e < 1), F i j e =
      (U j : ↥(upperHalfPlane K₀ K) → K) ((Matrix.ProjGenLinGroup.mk (g i)) • ⟨(b i : K) + e, add_mem_upperHalfPlane Q (hb i) he⟩) /
        (U j : ↥(upperHalfPlane K₀ K) → K) ((Matrix.ProjGenLinGroup.mk (g i)) • (b i)) := by
    intro i j e he
    simp only [F, dif_pos he]
  have hv0 : Valued.v (0 : K) < 1 := by rw [map_zero]; exact zero_lt_one
  have hF0 : ∀ i j, F i j 0 = 1 := by
    intro i j
    rw [hFdef i j 0 hv0]
    have : (⟨(b i : K) + 0, add_mem_upperHalfPlane Q (hb i) hv0⟩ : ↥(upperHalfPlane K₀ K)) = b i := Subtype.ext (add_zero _)
    rw [this]
    exact div_self (hUne _ _)

  have h0 : ∀ (i j : Fin r) (e : K), Valued.v e < 1 → Valued.v (F i j e - F i j 0 - d i j * e) ≤ Valued.v e ^ 2 := by
    intro i j e he
    rw [hF0, hFdef i j e he]
    have hz : Valued.v (((⟨(b i : K) + e, add_mem_upperHalfPlane Q (hb i) he⟩ : ↥(upperHalfPlane K₀ K)) : K) - (b i : K)) < 1 := by
      show Valued.v ((b i : K) + e - (b i : K)) < 1
      rwa [add_sub_cancel_left]
    have hp := hpin i j ⟨(b i : K) + e, add_mem_upperHalfPlane Q (hb i) he⟩ hz
    have hsub : (((⟨(b i : K) + e, add_mem_upperHalfPlane Q (hb i) he⟩ : ↥(upperHalfPlane K₀ K)) : K) - (b i : K)) = e := by
      show (b i : K) + e - (b i : K) = e
      rw [add_sub_cancel_left]
    rw [hsub] at hp
    have hc : (U j : ↥(upperHalfPlane K₀ K) → K) ((Matrix.ProjGenLinGroup.mk (g i)) • (b i)) ≠ 0 := hUne _ _
    have halg : (U j : ↥(upperHalfPlane K₀ K) → K) ((Matrix.ProjGenLinGroup.mk (g i)) • ⟨(b i : K) + e, add_mem_upperHalfPlane Q (hb i) he⟩) /
          (U j : ↥(upperHalfPlane K₀ K) → K) ((Matrix.ProjGenLinGroup.mk (g i)) • (b i)) - 1 - d i j * e =
        ((U j : ↥(upperHalfPlane K₀ K) → K) ((Matrix.ProjGenLinGroup.mk (g i)) • ⟨(b i : K) + e, add_mem_upperHalfPlane Q (hb i) he⟩) -
          (U j : ↥(upperHalfPlane K₀ K) → K) ((Matrix.ProjGenLinGroup.mk (g i)) • (b i)) * (1 + d i j * e)) /
          (U j : ↥(upperHalfPlane K₀ K) → K) ((Matrix.ProjGenLinGroup.mk (g i)) • (b i)) := by
      field_simp
      ring
    rw [halg, map_div₀, div_le_iff₀ (pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).mpr hc)),
      mul_comm (Valued.v e ^ 2) _]
    exact hp
  have hcen : ∀ (i j : Fin r) (e' : K), Valued.v e' < 1 → ∃ d' : K, ∀ e : K, Valued.v e < 1 →
      Valued.v (F i j e - F i j e' - d' * (e - e')) ≤ Valued.v (e - e') ^ 2 := by
    intro i j e' he'
    obtain ⟨d', -, hd'⟩ := holPins Q (U j) (hU j) (g i) (b i) (hb i) e' he'
    exact ⟨d', fun e he => by rw [hFdef i j e he, hFdef i j e' he']; exact hd' e he⟩
  have hF : ∀ (i j : Fin r) (e e' : K) (s t : Γ₀), s < 1 → Valued.v e ≤ s → Valued.v e' ≤ s →
      Valued.v (e - e') ≤ t → Valued.v (F i j e - F i j e' - d i j * (e - e')) ≤ t * s :=
    fun i j e e' s t hs he he' hee' => lipschitz_of_pins (F i j) (d i j) (h0 i j) (hcen i j) e e' s t hs he he' hee'
  obtain ⟨hR0, hR⟩ := Valued.v_prod_sub_one_sub_sum_sub_le_of_forall_v_sub_sub_mul_sub_le F d hd hF0 hF

  by_cases hr : r = 0
  · subst hr
    exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun j => j.elim0⟩
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin r)) (fun j => Valued.v (y j - 1))
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.pos_of_ne_zero hr⟩⟩)
  set s : Γ₀ := Valued.v (y j₀ - 1) with hsdef
  have hs : s < 1 := hy j₀
  have hys : ∀ j, Valued.v (y j - 1) ≤ s := fun j => hj₀ j (Finset.mem_univ j)

  let A : Matrix (Fin r) (Fin r) K := Matrix.of fun j i => d i j
  have hA : ∀ j i : Fin r, Valued.v (A j i) ≤ 1 := fun j i => hd i j
  have hAdet : Valued.v A.det = 1 := by
    have : A = d.transpose := rfl
    rw [this, Matrix.det_transpose]
    exact hdet
  let R : (Fin r → K) → (Fin r → K) := fun ε j => (∏ i, F i j (ε i)) - 1 - ∑ i, d i j * ε i
  have hR0' : R 0 = 0 := funext fun j => hR0 j
  have hR' : ∀ (ε ε' : Fin r → K) (s t : Γ₀), s < 1 → (∀ j, Valued.v (ε j) ≤ s) → (∀ j, Valued.v (ε' j) ≤ s) →
      (∀ j, Valued.v (ε j - ε' j) ≤ t) → ∀ i, Valued.v (R ε i - R ε' i) ≤ t * s :=
    fun ε ε' s t hs hε hε' hεε' i => hR ε ε' s t hs hε hε' hεε' i
  obtain ⟨ε, hεs, hsol⟩ := Valued.exists_mulVec_add_eq_of_v_det_eq_one hrk A hA hAdet R hR0' hR'
    (fun j => y j - 1) s hs hys
  have hεlt : ∀ i, Valued.v (ε i) < 1 := fun i => lt_of_le_of_lt (hεs i) hs
  refine ⟨ε, fun i => add_mem_upperHalfPlane Q (hb i) (hεlt i), hεlt, fun j => ?_⟩
  have hj := congrFun hsol j
  have hmv : A.mulVec ε j = ∑ i, d i j * ε i := rfl
  rw [Pi.add_apply, hmv] at hj
  have hprod : ∏ i, F i j (ε i) = y j := by
    change (∑ i, d i j * ε i) + ((∏ i, F i j (ε i)) - 1 - ∑ i, d i j * ε i) = y j - 1 at hj
    linear_combination hj
  rw [← hprod]
  exact Finset.prod_congr rfl fun i _ => (hFdef i j (ε i) (hεlt i)).symm

theorem finite_orbit_pullback (Q : PseudoUniformizer K₀ K) (hex : IsExhausted Q)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hdisc : IsDiscrete K ρ)
    {x : K} (hx : x ∈ upperHalfPlane K₀ K) (g : GL (Fin 2) K₀) :
    Set.Finite {z : K | z ∈ Set.range (fun γ : G => pmoebius K₀ (ρ γ) x) ∧
      pmoebius K₀ (Matrix.ProjGenLinGroup.mk g)⁻¹ z ∈ affinoid Q 0} := by
  obtain ⟨m, hm⟩ := exists_mapsTo_affinoid Q (Matrix.ProjGenLinGroup.mk g) 0
  obtain ⟨n₀, hn₀⟩ := hex x hx
  have hxM : x ∈ affinoid Q (max m n₀) := affinoid_mono Q (le_max_right _ _) hn₀
  have hS := CerednikDrinfeld.Omega.finite_setOf_pmoebius_mem_affinoid Q ρ hdisc (max m n₀) hxM
  refine (hS.image (fun γ : G => pmoebius K₀ (ρ γ) x)).subset ?_
  rintro z ⟨⟨γ, rfl⟩, hz⟩
  refine ⟨γ, ?_, rfl⟩
  simp only [Set.mem_setOf_eq]
  have hzΩ : pmoebius K₀ (ρ γ) x ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ hx _
  have hback : pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g)⁻¹ (pmoebius K₀ (ρ γ) x)) =
      pmoebius K₀ (ρ γ) x := by
    rw [← pmoebius_mul K₀ hzΩ, mul_inv_cancel, pmoebius_one]
  rw [← hback]
  exact affinoid_mono Q (le_max_left _ _) (hm hz)

end JC3d

theorem solution
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (ϖ₁ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ₁) [IsDomain ↥(holRing ϖ₁)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀))
    [MulAction G (LT.LatticeTree.Vertex R K₀)]
    [CerednikDrinfeld.Mumford.GraphAction G (CerednikDrinfeld.BruhatTits.tree R K₀)]
    (hρ : CerednikDrinfeld.Mumford.ActsThrough (LT.LatticeTree.Vertex R K₀) ρ)

    (hfin : ∀ w : LT.LatticeTree.Vertex R K₀, Finite (MulAction.stabilizer G w))
    [Finite (CerednikDrinfeld.Mumford.QuotVert G (LT.LatticeTree.Vertex R K₀))]
    (τ : LT.LatticeTree.Vertex R K₀ → ZMod 2) (hτ : ∀ (g : G) (w : LT.LatticeTree.Vertex R K₀), τ (g • w) = τ w)
    (hadj : ∀ u w : LT.LatticeTree.Vertex R K₀, (CerednikDrinfeld.BruhatTits.tree R K₀).Adj u w → τ u ≠ τ w)
    (htame : ∀ w : LT.LatticeTree.Vertex R K₀, Valued.v ((Nat.card ↥(MulAction.stabilizer G w) : ℕ) : K) = 1)

    (z₀ : K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)

    (θ : G →* Kˣ) (hθ₁ : ∀ β : G, Valued.v (((θ β : Kˣ) : K) - 1) < 1) (hθ : ∀ γ : G, IsOfFinOrder γ → θ γ = 1) :
    ∃ (n : ℕ) (a b : Fin n → K),
      (∀ i, a i ∈ upperHalfPlane K₀ K) ∧ (∀ i, b i ∈ upperHalfPlane K₀ K) ∧
      (∀ i (γ : G), pmoebius K₀ (ρ γ) (a i) ≠ z₀) ∧ (∀ i (γ : G), pmoebius K₀ (ρ γ) (b i) ≠ z₀) ∧
      ∀ β : G, ((θ β : Kˣ) : K) = ∏ i, theta ρ (a i) (b i) z₀ (pmoebius K₀ (ρ β) z₀) := by
  classical

  have hst : {γ : G | ρ γ • LT.LatticeTree.stdVertex R K₀ = LT.LatticeTree.stdVertex R K₀}.Finite := by
    haveI := hfin (LT.LatticeTree.stdVertex R K₀)
    have hset : {γ : G | ρ γ • LT.LatticeTree.stdVertex R K₀ = LT.LatticeTree.stdVertex R K₀} =
        ((MulAction.stabilizer G (LT.LatticeTree.stdVertex R K₀) : Subgroup G) : Set G) := by
      ext γ
      simp only [Set.mem_setOf_eq, SetLike.mem_coe, MulAction.mem_stabilizer_iff, hρ γ]
    rw [hset]
    exact Set.toFinite _
  have hdisc : IsDiscrete K ρ :=
    CerednikDrinfeld.Omega.isDiscrete_of_finite_stabilizer_stdVertex R K₀ ϖ hϖ K hint hv hq ρ hst
  obtain ⟨w, hw, hwz₀⟩ := JC3d.exists_mem_upperHalfPlane_forall_pmoebius_ne ϖ₁ hex ρ hdisc hz₀
  haveI hfinE : Finite (CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀)) :=
    CerednikDrinfeld.BruhatTits.finite_quotEdge_of_finite_quotVert R K₀ ϖ hϖ (G := G)
  let E : Type := {e : CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀) // τ e.out.fst = 0}
  haveI : Fintype E := Fintype.ofFinite E
  let eE : E ≃ {e : CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀) // τ e.out.fst = 0} :=
    Equiv.refl _

  obtain ⟨r, βv, ι, hι, hunimod, hspan⟩ :=
    CerednikDrinfeld.Omega.exists_isUnit_det_pathCycle_and_span_pathCycle R K₀ ϖ hϖ K hint hv hq hrk ϖ₁ hex ρ hρ hfin
      τ hτ hadj htame eE

  have hUex : ∀ j : Fin r, ∃ U : ↥(holRing ϖ₁), IsUnit U ∧
      ∀ z : ↥(upperHalfPlane K₀ K), (¬ ∃ γ : G, pmoebius K₀ (ρ γ) z₀ = (z : K)) →
        (U : ↥(upperHalfPlane K₀ K) → K) z = theta ρ z₀ (pmoebius K₀ (ρ (βv j)) z₀) w (z : K) := by
    intro j
    obtain ⟨U, hU1, -, hU3, -⟩ := CerednikDrinfeld.Omega.exists_isUnit_coe_eq_thetaMer_apply_smul_eq_period_mul
      K₀ K ϖ₁ hex ρ hdisc hz₀ hw hwz₀ (βv j)
    exact ⟨U, hU1, hU3⟩
  choose U hU hUθ using hUex

  let Z : Set K := Set.range (fun γ : G => pmoebius K₀ (ρ γ) z₀)
  have hZ : ∀ g : GL (Fin 2) K₀,
      Set.Finite {z : K | z ∈ Z ∧ pmoebius K₀ (Matrix.ProjGenLinGroup.mk g)⁻¹ z ∈ affinoid ϖ₁ 0} :=
    fun g => JC3d.finite_orbit_pullback ϖ₁ hex ρ hdisc hz₀ g
  obtain ⟨g, b, d, hbaff, havoid, hd1, hdet, hpin⟩ :=
    CerednikDrinfeld.Omega.exists_v_det_eq_one_of_isUnit_det_pathCycle_of_finite R K₀ ϖ hϖ K hint hv hq hrk ϖ₁ hex ρ hρ
      hfin τ hτ hadj htame eE hz₀ hw hwz₀ βv ι hι hunimod U hU hUθ Z hZ

  obtain ⟨ε, hεΩ, hεlt, hsolve⟩ := JC3d.newtonSolve hrk ϖ₁ U hU g b d hbaff hd1 hdet hpin
    (fun j => ((θ (βv j) : Kˣ) : K)) (fun j => hθ₁ (βv j))

  let P : Fin r → ↥(upperHalfPlane K₀ K) := fun i => (Matrix.ProjGenLinGroup.mk (g i)) • (b i)
  let Q : Fin r → ↥(upperHalfPlane K₀ K) := fun i => (Matrix.ProjGenLinGroup.mk (g i)) • ⟨(b i : K) + ε i, hεΩ i⟩
  have hPdef : ∀ i, P i = (Matrix.ProjGenLinGroup.mk (g i)) • (b i) := fun i => rfl
  have hQdef : ∀ i, Q i = (Matrix.ProjGenLinGroup.mk (g i)) • ⟨(b i : K) + ε i, hεΩ i⟩ := fun i => rfl

  have hpull : ∀ (i : Fin r) (γ : G) (x : ↥(upperHalfPlane K₀ K)),
      pmoebius K₀ (ρ γ) (((Matrix.ProjGenLinGroup.mk (g i)) • x : ↥(upperHalfPlane K₀ K)) : K) = z₀ →
        (Matrix.ProjGenLinGroup.mk (g i))⁻¹ • ((ρ γ⁻¹) • (⟨z₀, hz₀⟩ : ↥(upperHalfPlane K₀ K))) = x := by
    intro i γ x h
    have h1 : (ρ γ) • ((Matrix.ProjGenLinGroup.mk (g i)) • x) = (⟨z₀, hz₀⟩ : ↥(upperHalfPlane K₀ K)) :=
      Subtype.ext (by rw [coe_smul_upperHalfPlane]; exact h)
    rw [← h1, map_inv, inv_smul_smul, inv_smul_smul]
  have hmemZ : ∀ γ : G, pmoebius K₀ (ρ γ⁻¹) z₀ ∈ Z := fun γ => ⟨γ⁻¹, rfl⟩
  have hcoe : ∀ (i : Fin r) (γ : G),
      (((Matrix.ProjGenLinGroup.mk (g i))⁻¹ • ((ρ γ⁻¹) • (⟨z₀, hz₀⟩ : ↥(upperHalfPlane K₀ K))) : ↥(upperHalfPlane K₀ K)) : K) =
        pmoebius K₀ (Matrix.ProjGenLinGroup.mk (g i))⁻¹ (pmoebius K₀ (ρ γ⁻¹) z₀) := by
    intro i γ
    rw [coe_smul_upperHalfPlane, coe_smul_upperHalfPlane]
  have hPav : ∀ (i : Fin r) (γ : G), pmoebius K₀ (ρ γ) ((P i : ↥(upperHalfPlane K₀ K)) : K) ≠ z₀ := by
    intro i γ h
    have h2 := congrArg (fun x : ↥(upperHalfPlane K₀ K) => (x : K)) (hpull i γ (b i) h)
    beta_reduce at h2
    rw [hcoe] at h2
    have h3 := havoid i _ (hmemZ γ)
    rw [h2, sub_self, map_zero] at h3
    exact absurd h3 (not_le.mpr zero_lt_one)
  have hQav : ∀ (i : Fin r) (γ : G), pmoebius K₀ (ρ γ) ((Q i : ↥(upperHalfPlane K₀ K)) : K) ≠ z₀ := by
    intro i γ h
    have h2 := congrArg (fun x : ↥(upperHalfPlane K₀ K) => (x : K)) (hpull i γ ⟨(b i : K) + ε i, hεΩ i⟩ h)
    simp only at h2
    rw [hcoe] at h2
    have h3 := havoid i _ (hmemZ γ)
    rw [h2] at h3
    simp only [add_sub_cancel_left] at h3
    exact absurd (lt_of_lt_of_le (hεlt i) h3) (lt_irrefl _)

  have hoff : ∀ x : ↥(upperHalfPlane K₀ K), (∀ γ : G, pmoebius K₀ (ρ γ) (x : K) ≠ z₀) →
      ¬ ∃ γ : G, pmoebius K₀ (ρ γ) z₀ = (x : K) := by
    intro x hx ⟨γ, hγ⟩
    apply hx γ⁻¹
    have : (ρ γ) • (⟨z₀, hz₀⟩ : ↥(upperHalfPlane K₀ K)) = x := Subtype.ext (by rw [coe_smul_upperHalfPlane]; exact hγ)
    rw [← coe_smul_upperHalfPlane, ← this, map_inv, inv_smul_smul]

  have hUne : ∀ (j : Fin r) (x : ↥(upperHalfPlane K₀ K)), (U j : ↥(upperHalfPlane K₀ K) → K) x ≠ 0 :=
    fun j x => JC3d.apply_ne_zero_of_isUnit ϖ₁ (U j) (hU j) x
  have hmult : ∀ (i j : Fin r),
      theta ρ (P i : K) (Q i : K) z₀ (pmoebius K₀ (ρ (βv j)) z₀) =
        (U j : ↥(upperHalfPlane K₀ K) → K) (Q i) / (U j : ↥(upperHalfPlane K₀ K) → K) (P i) := by
    intro i j
    have h4 := CerednikDrinfeld.Omega.theta_pmoebius_mul_theta_eq_theta ρ (P i).2 (Q i).2 hz₀ hw (hPav i) (hQav i) hwz₀ (βv j)
      (JC3d.thetaMultipliable ϖ₁ hex ρ hdisc (P i).2 (Q i).2 hz₀ (pmoebius_mem_upperHalfPlane K₀ hz₀ _))
      (JC3d.thetaMultipliable ϖ₁ hex ρ hdisc hz₀ (pmoebius_mem_upperHalfPlane K₀ hz₀ _) hw (P i).2)
    rw [← hUθ j (P i) (hoff (P i) (hPav i)), ← hUθ j (Q i) (hoff (Q i) (hQav i))] at h4
    rw [eq_div_iff (hUne j (P i))]
    exact h4

  obtain ⟨c, hc, hct⟩ := JC3d.exists_monoidHom_prod_theta ϖ₁ hex ρ hdisc hz₀ r (fun i => (P i : K)) (fun i => (Q i : K))
    (fun i => (P i).2) (fun i => (Q i).2) hPav hQav
  have hcβ : ∀ j : Fin r, c (βv j) = θ (βv j) := by
    intro j
    apply Units.ext
    rw [hc (βv j), ← hsolve j]
    exact Finset.prod_congr rfl fun i _ => hmult i j
  have hcθ : c = θ :=
    CerednikDrinfeld.Omega.monoidHom_eq_of_forall_isOfFinOrder_of_forall_apply_eq_of_span_pathCycle R K₀ ϖ hϖ K hint hv hq hrk
      ϖ₁ hex ρ hρ hfin τ hτ hadj htame eE βv hspan c θ hct hθ hcβ

  refine ⟨r, fun i => (P i : K), fun i => (Q i : K), fun i => (P i).2, fun i => (Q i).2, hPav, hQav, fun β => ?_⟩
  rw [← hcθ]
  exact hc β

end S_CerednikDrinfeld_Omega_exists_points_prod_theta_eq_of_v_sub_one_lt
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_points_prod_theta_eq_of_v_sub_one_lt (solution)
