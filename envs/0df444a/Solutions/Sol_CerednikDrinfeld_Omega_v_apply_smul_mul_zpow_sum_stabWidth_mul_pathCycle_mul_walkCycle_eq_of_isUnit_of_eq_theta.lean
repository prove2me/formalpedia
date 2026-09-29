-- Prove2me | solution 1 for CerednikDrinfeld.Omega.v_apply_smul_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq_of_isUnit_of_eq_theta
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/e3ea47fb-ba63-5c1b-af49-6041bc4b3d17

import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Theorems.Thm_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq
import Theorems.Thm_CerednikDrinfeld_Omega_v_apply_eq_of_mem_holOn_affinoid_zero_of_mul_eq_one
import Theorems.Thm_CerednikDrinfeld_Omega_finite_setOf_pmoebius_mem_affinoid
import Theorems.Thm_CerednikDrinfeld_Omega_isDiscrete_of_finite_stabilizer_stdVertex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_v_apply_smul_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq_of_isUnit_of_eq_theta
p2m_attr_erase "simp" "LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq CerednikDrinfeld.Mumford.walkOverlap_nil_right CerednikDrinfeld.Mumford.walkOverlap_nil_left LocalGL2.swapUnit_val"

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_v_apply_smul_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq_of_isUnit_of_eq_theta.CerednikDrinfeld CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_v_apply_smul_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq_of_isUnit_of_eq_theta.CerednikDrinfeld.Omega CerednikDrinfeld.Mumford MulAction"

noncomputable section

namespace EPVgen

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
  {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
  {G : Type} [Group G]

theorem finite_setOf_mem_affinoid_and_exists_pmoebius_eq
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ) (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    (g : PGL(2, K₀)) (n : ℕ) {y : K} (hy : y ∈ upperHalfPlane K₀ K) :
    {ζ : K | ζ ∈ affinoid ϖ n ∧ ∃ γ : G, pmoebius K₀ (ρ γ) y = pmoebius K₀ g ζ}.Finite := by
  obtain ⟨m, hm⟩ := exists_mapsTo_affinoid ϖ g n
  obtain ⟨m', hm'⟩ := hex y hy
  set N := max m m' with hN
  have hyN : y ∈ affinoid ϖ N := affinoid_mono ϖ (le_max_right _ _) hm'
  have hfin := finite_setOf_pmoebius_mem_affinoid ϖ ρ hρ N hyN
  refine (hfin.image fun γ => pmoebius K₀ g⁻¹ (pmoebius K₀ (ρ γ) y)).subset ?_
  rintro ζ ⟨hζ, γ, hγ⟩
  have hζΩ : ζ ∈ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ n hζ
  refine ⟨γ, ?_, ?_⟩
  · show pmoebius K₀ (ρ γ) y ∈ affinoid ϖ N
    rw [hγ]; exact affinoid_mono ϖ (le_max_left _ _) (hm hζ)
  · show pmoebius K₀ g⁻¹ (pmoebius K₀ (ρ γ) y) = ζ
    rw [hγ, ← pmoebius_mul K₀ hζΩ, inv_mul_cancel, pmoebius_one]

theorem exists_mem_ball_forall_ne
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ) (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    (g : PGL(2, K₀)) (n : ℕ) {x₀ c : K} (hc : c ≠ 0)
    (hball : ∀ ζ : K, Valued.v (ζ - x₀) < Valued.v c → ζ ∈ affinoid ϖ n)
    (Y : Finset K) (hY : ∀ y ∈ Y, y ∈ upperHalfPlane K₀ K) (B : Finset K) :
    ∃ ζ : K, Valued.v (ζ - x₀) < Valued.v c ∧ ζ ∉ B ∧
      ∀ y ∈ Y, ∀ γ : G, pmoebius K₀ (ρ γ) y ≠ pmoebius K₀ g ζ := by
  classical

  have hbad : {ζ : K | ζ ∈ affinoid ϖ n ∧ ∃ y ∈ Y, ∃ γ : G, pmoebius K₀ (ρ γ) y = pmoebius K₀ g ζ}.Finite := by
    refine (Set.Finite.biUnion (Finset.finite_toSet Y) fun y hy =>
      finite_setOf_mem_affinoid_and_exists_pmoebius_eq ϖ hex ρ hρ g n (hY y hy)).subset ?_
    rintro ζ ⟨hζ, y, hy, γ, hγ⟩
    exact Set.mem_biUnion hy ⟨hζ, γ, hγ⟩

  have hp0 : algebraMap K₀ K ϖ.ϖ ≠ 0 := (Valuation.ne_zero_iff _).1 ϖ.pos.ne'
  have hp1 : Valued.v (algebraMap K₀ K ϖ.ϖ) < 1 := ϖ.lt_one
  let s : ℕ → K := fun k => x₀ + c * algebraMap K₀ K ϖ.ϖ ^ (k + 1)
  have hs_inj : Function.Injective s := by
    intro i j hij
    have h1 := mul_left_cancel₀ hc (add_left_cancel hij)
    have h2 : Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (i + 1) = Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (j + 1) := by
      have := congrArg (Valued.v (R := K) (Γ₀ := Γ₀)) h1
      simpa only [Valuation.map_pow] using this
    exact Nat.succ_injective (pow_right_injective₀ ϖ.pos hp1.ne h2)
  have hs_ball : ∀ k, Valued.v (s k - x₀) < Valued.v c := fun k => by
    show Valued.v (x₀ + c * algebraMap K₀ K ϖ.ϖ ^ (k + 1) - x₀) < Valued.v c
    rw [add_sub_cancel_left, map_mul, map_pow]
    exact mul_lt_of_lt_one_right ((Valuation.pos_iff _).2 hc) (pow_lt_one₀ zero_le' hp1 (Nat.succ_ne_zero k))
  have hinf : {ζ : K | Valued.v (ζ - x₀) < Valued.v c}.Infinite :=
    Set.infinite_of_injective_forall_mem hs_inj hs_ball
  obtain ⟨ζ, hζ, hζnot⟩ := (hinf.diff (hbad.union (Finset.finite_toSet B))).nonempty
  refine ⟨ζ, hζ, fun hB => hζnot (Or.inr hB), fun y hy γ hγ => hζnot (Or.inl ⟨hball ζ hζ, y, hy, γ, hγ⟩)⟩

end EPVgen

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Mumford.ActsThrough Mumford.walkCycle Mumford.pathCycle Mumford.GraphAction Mumford.QuotEdge Mumford.QuotVert Mumford.stabWidth tree BruhatTits.tree Omega.v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq"
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "PseudoUniformizer affinoid affinoid_subset_upperHalfPlane affinoid_mono mem_affinoid_iff' IsExhausted IsHolOn restrictAffinoid holRing mem_holRing_iff coe_smul_upperHalfPlane exists_mapsTo_affinoid coe_smul_holRing_apply pmoebius upperHalfPlane pmoebius_one pmoebius_mul theta IsDiscrete v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq v_apply_eq_of_mem_holOn_affinoid_zero_of_mul_eq_one finite_setOf_pmoebius_mem_affinoid isDiscrete_of_finite_stabilizer_stdVertex"
namespace GlobalCurrent
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

section HolRingCofinal

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem IsHolOn.comp_inclusion {S S' : Set K} (h : S' ⊆ S) {f : ↥S → K} (hf : IsHolOn K S f) :
    IsHolOn K S' (f ∘ Set.inclusion h) := by
  obtain ⟨r, hr, ⟨b, hb⟩, hlim⟩ := hf
  exact ⟨r, fun k z hz => hr k z (h hz), ⟨b, fun k z => hb k (Set.inclusion h z)⟩, hlim.comp (Set.inclusion h)⟩

theorem PseudoUniformizer.ϖ_ne_zero (ϖ : PseudoUniformizer K₀ K) : ϖ.ϖ ≠ 0 := by
  intro h
  have := ϖ.pos
  rw [h, map_zero, Valuation.map_zero] at this
  exact lt_irrefl _ this

theorem exists_affinoid_subset_affinoid (ϖ ϖ' : PseudoUniformizer K₀ K) (n : ℕ) :
    ∃ m : ℕ, affinoid ϖ' n ⊆ affinoid ϖ m := by
  obtain ⟨N, hN, -⟩ := ϖ.scale (ϖ'.ϖ ^ n) (pow_ne_zero n (PseudoUniformizer.ϖ_ne_zero ϖ'))
  rw [map_pow, Valuation.map_pow] at hN

  have hinv : (Valued.v (algebraMap K₀ K ϖ'.ϖ))⁻¹ ^ n ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ N := by
    rw [inv_pow, inv_pow]
    exact inv_anti₀ (pow_pos ϖ.pos N) hN
  refine ⟨N, fun z hz => ?_⟩
  rw [mem_affinoid_iff'] at hz ⊢
  exact ⟨hz.1.trans hinv, fun a => hN.trans (hz.2 a)⟩

theorem holRing_le_holRing (ϖ ϖ' : PseudoUniformizer K₀ K) : holRing ϖ ≤ holRing ϖ' := by
  intro f hf n
  obtain ⟨m, hm⟩ := exists_affinoid_subset_affinoid ϖ ϖ' n
  exact IsHolOn.comp_inclusion hm (hf m)

theorem holRing_eq_holRing (ϖ ϖ' : PseudoUniformizer K₀ K) : holRing ϖ = holRing ϖ' :=
  le_antisymm (holRing_le_holRing ϖ ϖ') (holRing_le_holRing ϖ' ϖ)

theorem affinoid_zero_eq (ϖa ϖb : PseudoUniformizer K₀ K) : affinoid ϖa 0 = affinoid ϖb 0 := by
  ext z
  simp only [affinoid, pow_zero, Set.mem_setOf_eq]

theorem v_apply_eq_of_isUnit [DecidableEq K] [IsAlgClosed K] (Q : PseudoUniformizer K₀ K) (F : ↥(holRing Q))
    (hF : IsUnit F) {w w' : K} (hw : w ∈ affinoid Q 0) (hw' : w' ∈ affinoid Q 0) :
    Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) ⟨w, affinoid_subset_upperHalfPlane Q 0 hw⟩) =
      Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) ⟨w', affinoid_subset_upperHalfPlane Q 0 hw'⟩) := by
  obtain ⟨G, hFG⟩ := hF.exists_right_inv
  have hprod : restrictAffinoid Q 0 (F : ↥(upperHalfPlane K₀ K) → K) * restrictAffinoid Q 0 (G : ↥(upperHalfPlane K₀ K) → K) = 1 := by
    funext z
    have := congrArg (fun H : ↥(holRing Q) => (H : ↥(upperHalfPlane K₀ K) → K) (Set.inclusion (affinoid_subset_upperHalfPlane Q 0) z)) hFG
    simpa [restrictAffinoid] using this
  exact v_apply_eq_of_mem_holOn_affinoid_zero_of_mul_eq_one Q ((mem_holRing_iff Q _).1 F.2 0) ((mem_holRing_iff Q _).1 G.2 0)
    hprod ⟨w, hw⟩ ⟨w', hw'⟩

end HolRingCofinal

section Translates

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

def omegaTranslate (Q : PseudoUniformizer K₀ K) (F : ↥(holRing Q)) (g : PGL(2, K₀)) : ↥(holRing Q) := g⁻¹ • F

theorem omegaTranslate_apply (Q : PseudoUniformizer K₀ K) (F : ↥(holRing Q)) (g : PGL(2, K₀)) (z : ↥(upperHalfPlane K₀ K)) :
    (omegaTranslate Q F g : ↥(upperHalfPlane K₀ K) → K) z = (F : ↥(upperHalfPlane K₀ K) → K) (g • z) := by
  rw [omegaTranslate, coe_smul_holRing_apply, inv_inv]

theorem isUnit_omegaTranslate (Q : PseudoUniformizer K₀ K) {F : ↥(holRing Q)} (hF : IsUnit F) (g : PGL(2, K₀)) :
    IsUnit (omegaTranslate Q F g) :=
  hF.map (MulSemiringAction.toRingHom _ ↥(holRing Q) g⁻¹)

end Translates

end CerednikDrinfeld.Omega.GlobalCurrent

open CerednikDrinfeld.Omega.GlobalCurrent EPVgen in
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

    [DecidableEq (CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀))]
    {E : Type} [Fintype E]
    (eE : E ≃ {e : CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀) // τ e.out.fst = 0})
    [DecidableEq (LT.LatticeTree.Vertex R K₀)]

    {a z₁ : K} (ha : a ∈ upperHalfPlane K₀ K) (hz₁ : z₁ ∈ upperHalfPlane K₀ K)
    (hz₁a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₁) (β : G)
    (U : ↥(holRing ϖ₁)) (hU : IsUnit U)
    (hUθ : ∀ z : ↥(upperHalfPlane K₀ K), (¬ ∃ γ : G, pmoebius K₀ (ρ γ) a = (z : K)) →
      (U : ↥(upperHalfPlane K₀ K) → K) z = theta ρ a (pmoebius K₀ (ρ β) a) z₁ (z : K))

    (g g' : GL (Fin 2) K₀) (w w' : K) (hw : w ∈ affinoid ϖ₁ 0) (hw' : w' ∈ affinoid ϖ₁ 0)
    (p : (CerednikDrinfeld.BruhatTits.tree R K₀).Walk (g • LT.LatticeTree.stdVertex R K₀) (g' • LT.LatticeTree.stdVertex R K₀)) :
    Valued.v ((U : ↥(upperHalfPlane K₀ K) → K)
        ((Matrix.ProjGenLinGroup.mk g') • ⟨w', affinoid_subset_upperHalfPlane ϖ₁ 0 hw'⟩)) *
        Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^
          (∑ e : E, ((CerednikDrinfeld.Mumford.stabWidth G (CerednikDrinfeld.BruhatTits.tree R K₀) (eE e).1 : ℕ) : ℤ) *
            CerednikDrinfeld.Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => (eE e').1)
              (LT.LatticeTree.stdVertex R K₀) β e *
            CerednikDrinfeld.Mumford.walkCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => (eE e').1) p e) =
      Valued.v ((U : ↥(upperHalfPlane K₀ K) → K)
        ((Matrix.ProjGenLinGroup.mk g) • ⟨w, affinoid_subset_upperHalfPlane ϖ₁ 0 hw⟩)) := by
  classical

  have hdisc : IsDiscrete K ρ := by
    refine isDiscrete_of_finite_stabilizer_stdVertex R K₀ ϖ hϖ K hint hv hq ρ ?_
    have : {γ : G | ρ γ • LT.LatticeTree.stdVertex R K₀ = LT.LatticeTree.stdVertex R K₀}
        = (stabilizer G (LT.LatticeTree.stdVertex R K₀) : Set G) := by
      ext γ; simp only [Set.mem_setOf_eq, SetLike.mem_coe, mem_stabilizer_iff, hρ γ]
    rw [this]; exact Set.toFinite _

  have hball : ∀ {x : K}, x ∈ affinoid ϖ₁ 0 → ∀ ζ : K, Valued.v (ζ - x) < Valued.v (1 : K) → ζ ∈ affinoid ϖ₁ 0 := by
    intro x hx ζ hζ
    rw [map_one] at hζ
    rw [mem_affinoid_iff'] at hx ⊢
    obtain ⟨hx1, hx2⟩ := hx
    simp only [pow_zero] at hx1 hx2 ⊢
    refine ⟨?_, fun t => ?_⟩
    · have e : ζ = x + (ζ - x) := by ring
      rw [e]; exact (Valuation.map_add _ _ _).trans (max_le hx1 hζ.le)
    · have e : ζ - algebraMap K₀ K t = (x - algebraMap K₀ K t) + (ζ - x) := by ring
      rw [e, Valuation.map_add_eq_of_lt_left _ (hζ.trans_le (hx2 t))]; exact hx2 t

  obtain ⟨w₂, hw₂b, -, hw₂a⟩ := exists_mem_ball_forall_ne ϖ₁ hex ρ hdisc (Matrix.ProjGenLinGroup.mk g) 0
    (x₀ := w) (c := (1 : K)) one_ne_zero (hball hw) {a} (by simp [ha]) ∅
  obtain ⟨w₂', hw₂'b, -, hw₂'a⟩ := exists_mem_ball_forall_ne ϖ₁ hex ρ hdisc (Matrix.ProjGenLinGroup.mk g') 0
    (x₀ := w') (c := (1 : K)) one_ne_zero (hball hw') {a} (by simp [ha]) ∅
  have hw₂ : w₂ ∈ affinoid ϖ₁ 0 := hball hw w₂ hw₂b
  have hw₂' : w₂' ∈ affinoid ϖ₁ 0 := hball hw' w₂' hw₂'b
  have hga : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) w₂ := hw₂a a (Finset.mem_singleton_self a)
  have hg'a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ pmoebius K₀ (Matrix.ProjGenLinGroup.mk g') w₂' := hw₂'a a (Finset.mem_singleton_self a)

  have key := CerednikDrinfeld.Omega.v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq R K₀ ϖ hϖ K
    hint hv hq hrk ϖ₁ hex ρ hρ hfin τ hτ hadj htame eE a ha β z₁ hz₁ hz₁a g g' w₂ w₂' hw₂ hw₂' hga hg'a p

  have hU₂ := hUθ ((Matrix.ProjGenLinGroup.mk g) • ⟨w₂, affinoid_subset_upperHalfPlane ϖ₁ 0 hw₂⟩) (by
    rintro ⟨γ, hγ⟩; exact hga γ (by rw [hγ, coe_smul_upperHalfPlane]))
  have hU₂' := hUθ ((Matrix.ProjGenLinGroup.mk g') • ⟨w₂', affinoid_subset_upperHalfPlane ϖ₁ 0 hw₂'⟩) (by
    rintro ⟨γ, hγ⟩; exact hg'a γ (by rw [hγ, coe_smul_upperHalfPlane]))
  rw [coe_smul_upperHalfPlane] at hU₂ hU₂'
  rw [← hU₂, ← hU₂'] at key

  have hc := v_apply_eq_of_isUnit ϖ₁ (omegaTranslate ϖ₁ U (Matrix.ProjGenLinGroup.mk g))
    (isUnit_omegaTranslate ϖ₁ hU _) hw hw₂
  have hc' := v_apply_eq_of_isUnit ϖ₁ (omegaTranslate ϖ₁ U (Matrix.ProjGenLinGroup.mk g'))
    (isUnit_omegaTranslate ϖ₁ hU _) hw' hw₂'
  rw [omegaTranslate_apply, omegaTranslate_apply] at hc hc'
  rw [hc, hc']; exact key

end
end S_CerednikDrinfeld_Omega_v_apply_smul_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq_of_isUnit_of_eq_theta
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_v_apply_smul_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq_of_isUnit_of_eq_theta (solution)
