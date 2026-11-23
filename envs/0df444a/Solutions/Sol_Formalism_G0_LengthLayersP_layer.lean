-- Prove2me | solution 1 for Formalism.G0.LengthLayersP.layer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:46:39.324853+00:00
-- url     : https://prove2.me/submissions/b697fdd1-5aa2-4964-9b95-b7d843abd94e

import Definitions.Def_Formalism_SubspaceCounting_Statement
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_LengthLayers
import Theorems.Thm_Formalism_G0_LengthLayersP_length_eq_add_of_le
import Theorems.Thm_Formalism_G0_LengthLayersP_length_residue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
namespace Formalism.G0
namespace LengthLayersP
section General
variable {O : Type} [CommRing O]
end General
section DVR
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
private theorem length_sup_span_le_add_one_of_smul_mem (π : O) (hπ : Irreducible π) {X : Type} [AddCommGroup X]
    [Module O X] (W : Submodule O X) (z : X) (hz : π • z ∈ W) :
    Module.length O ↥(W ⊔ O ∙ z) ≤ Module.length O ↥W + 1 := by
  have hWT : W ≤ W ⊔ O ∙ z := le_sup_left
  rw [length_eq_add_of_le hWT]
  refine add_le_add le_rfl ?_
  set T := W ⊔ O ∙ z with hT
  set K := W.comap T.subtype with hK
  have hzT : z ∈ T := Submodule.mem_sup_right (Submodule.mem_span_singleton_self z)
  set q : ↥T ⧸ K := K.mkQ ⟨z, hzT⟩ with hq
  have hπq : π • q = 0 := by
    rw [hq, ← map_smul]
    exact (Submodule.Quotient.mk_eq_zero K).mpr hz
  let f : O →ₗ[O] ↥T ⧸ K := LinearMap.toSpanSingleton O _ q
  have hker : Ideal.span {π} ≤ LinearMap.ker f := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
    exact hπq
  have hsurj : Function.Surjective ((Ideal.span {π}).liftQ f hker) := by
    intro y
    obtain ⟨⟨t, ht⟩, rfl⟩ := K.mkQ_surjective y
    obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.mp ht
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hu
    refine ⟨Submodule.Quotient.mk r, ?_⟩
    rw [Submodule.liftQ_apply]
    show r • q = K.mkQ ⟨w + r • z, ht⟩
    rw [hq, ← map_smul]
    simp only [Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq, hK, Submodule.mem_comap]
    have e : T.subtype (r • ⟨z, hzT⟩ - ⟨w + r • z, ht⟩) = -w := by
      show r • z - (w + r • z) = -w
      abel
    rw [e]
    exact W.neg_mem hw
  exact (Module.length_le_of_surjective _ hsurj).trans (length_residue π hπ).le
private theorem length_sup_span_le_add_of_pow_smul_mem (π : O) (hπ : Irreducible π) {X : Type} [AddCommGroup X]
    [Module O X] : ∀ (s : ℕ) (W : Submodule O X) (z : X), π ^ s • z ∈ W →
      Module.length O ↥(W ⊔ O ∙ z) ≤ Module.length O ↥W + (s : ℕ∞) := by
  intro s
  induction s with
  | zero =>
    intro W z hz
    rw [pow_zero, one_smul] at hz
    have e : W ⊔ O ∙ z = W := sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr hz)
    rw [e]
    simp
  | succ s ih =>
    intro W z hz
    have h1 : π ^ s • (π • z) ∈ W := by rw [smul_smul, ← pow_succ]; exact hz
    have h2 := ih W (π • z) h1
    have h3 := length_sup_span_le_add_one_of_smul_mem π hπ (W ⊔ O ∙ (π • z)) z
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
    have h4 : W ⊔ O ∙ (π • z) ⊔ O ∙ z = W ⊔ O ∙ z := by
      apply le_antisymm
      · refine sup_le (sup_le le_sup_left ?_) le_sup_right
        exact le_trans ((Submodule.span_singleton_le_iff_mem _ _).mpr
          (Submodule.smul_mem _ π (Submodule.mem_span_singleton_self z))) le_sup_right
      · exact sup_le (le_trans le_sup_left le_sup_left) le_sup_right
    rw [h4] at h3
    calc Module.length O ↥(W ⊔ O ∙ z) ≤ Module.length O ↥(W ⊔ O ∙ (π • z)) + 1 := h3
      _ ≤ Module.length O ↥W + (s : ℕ∞) + 1 := add_le_add h2 le_rfl
      _ = Module.length O ↥W + ((s + 1 : ℕ) : ℕ∞) := by push_cast; ring
private theorem length_le_length_add_card_mul_of_pow_smul_mem (π : O) (hπ : Irreducible π) {X : Type} [AddCommGroup X]
    [Module O X] (s : ℕ) (C : Finset X) : ∀ (U V : Submodule O X), U ≤ V →
      V ≤ U ⊔ Submodule.span O (C : Set X) → (∀ v ∈ V, π ^ s • v ∈ U) →
      Module.length O ↥V ≤ Module.length O ↥U + ((C.card * s : ℕ) : ℕ∞) := by
  classical
  refine Finset.induction_on C ?_ ?_
  · intro U V hUV hV _
    rw [Finset.coe_empty, Submodule.span_empty, sup_bot_eq] at hV
    rw [le_antisymm hV hUV]
    simp
  · intro c C' hc ih U V hUV hV hs
    set W' := U ⊔ Submodule.span O (C' : Set X) with hW'
    set V' := V ⊓ W' with hV'
    have hUV' : U ≤ V' := le_inf hUV le_sup_left
    have h1 : Module.length O ↥V' ≤ Module.length O ↥U + ((C'.card * s : ℕ) : ℕ∞) :=
      ih U V' hUV' inf_le_right (fun v hv => hs v hv.1)
    let J : Ideal O := (V ⊔ W').comap (LinearMap.toSpanSingleton O X c)
    obtain ⟨j, hj⟩ := (IsPrincipalIdealRing.principal J).principal
    have hjJ : j ∈ J := by rw [hj]; exact Submodule.mem_span_singleton_self j
    have hjJ' := Submodule.mem_comap.mp hjJ
    rw [LinearMap.toSpanSingleton_apply] at hjJ'
    obtain ⟨vj, hvj, wj, hwj, hvw⟩ := Submodule.mem_sup.mp hjJ'
    have hVeq : V = V' ⊔ O ∙ vj := by
      apply le_antisymm
      · intro v hv
        have hv2 : v ∈ W' ⊔ O ∙ c := by
          have h5 := hV hv
          rw [Finset.coe_insert, Submodule.span_insert, sup_comm (O ∙ c), ← sup_assoc] at h5
          exact h5
        obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.mp hv2
        obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hy
        have hrJ : r ∈ J := by
          apply Submodule.mem_comap.mpr
          rw [LinearMap.toSpanSingleton_apply]
          have e : r • c = (w + r • c) + (-w) := by abel
          rw [e]
          exact Submodule.add_mem_sup hv (W'.neg_mem hw)
        rw [hj] at hrJ
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hrJ
        have e2 : (a • j) • c = a • vj + a • wj := by rw [smul_assoc, ← hvw, smul_add]
        have hdiff : w + (a • j) • c - a • vj ∈ V' := by
          refine ⟨V.sub_mem hv (V.smul_mem a hvj), ?_⟩
          have e3 : w + (a • j) • c - a • vj = w + a • wj := by rw [e2]; abel
          show w + (a • j) • c - a • vj ∈ W'
          rw [e3]
          exact W'.add_mem hw (W'.smul_mem a hwj)
        have e4 : w + (a • j) • c = (w + (a • j) • c - a • vj) + a • vj := by abel
        rw [e4]
        exact Submodule.add_mem_sup hdiff
          (Submodule.smul_mem _ a (Submodule.mem_span_singleton_self vj))
      · exact sup_le inf_le_left ((Submodule.span_singleton_le_iff_mem _ _).mpr hvj)
    have h2 : Module.length O ↥V ≤ Module.length O ↥V' + (s : ℕ∞) := by
      rw [hVeq]
      exact length_sup_span_le_add_of_pow_smul_mem π hπ s V' vj (hUV' (hs vj hvj))
    calc Module.length O ↥V ≤ Module.length O ↥V' + (s : ℕ∞) := h2
      _ ≤ Module.length O ↥U + ((C'.card * s : ℕ) : ℕ∞) + (s : ℕ∞) := add_le_add h1 le_rfl
      _ = Module.length O ↥U + (((insert c C').card * s : ℕ) : ℕ∞) := by
          rw [Finset.card_insert_of_notMem hc]; push_cast; ring
end DVR
section Main
variable {O : Type} [CommRing O]
end Main
end LengthLayersP
end Formalism.G0
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
open Formalism.G0.LengthLayersP
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace Formalism.G0.LengthLayersP
theorem _root_.solution (π : O) (hπ : Irreducible π) {X : Type} [AddCommGroup X] [Module O X]
    (U V : Submodule O X) (hUV : U ≤ V) (C : Finset X) (g s : ℕ) (hC : C.card ≤ g)
    (hV : V ≤ Submodule.span O (C : Set X)) (hs : ∀ v ∈ V, π ^ s • v ∈ U) :
    Module.length O ↥V ≤ Module.length O ↥U + ((g * s : ℕ) : ℕ∞) := by
  have h := length_le_length_add_card_mul_of_pow_smul_mem π hπ s C U V hUV (le_trans hV le_sup_right) hs
  refine le_trans h (add_le_add le_rfl ?_)
  exact_mod_cast Nat.mul_le_mul_right s hC
end Formalism.G0.LengthLayersP
