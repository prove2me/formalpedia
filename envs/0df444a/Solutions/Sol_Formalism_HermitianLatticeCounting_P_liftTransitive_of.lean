-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.liftTransitive_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:33.619285+00:00
-- url     : https://prove2.me/submissions/c6bd88ec-acbb-4caa-842e-f40b126c80b4

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_e_mem_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_isotropicSpan_le_jointSpan_left
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_isotropicSpan_le_jointSpan_right
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_lastVector_mem_jointSpan_left
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_lastVector_mem_jointSpan_right
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_GoodMap_inN
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_GoodMap_comp
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_good_family
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_repr_aniso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (hE : Formalism.HermitianLatticeCounting.S6.EichlerIsom) (hR : Formalism.HermitianLatticeCounting.S6.EichlerInR) :
    Formalism.HermitianLatticeCounting.S6.LiftTransitive := by
  intro K V _ _ _ _ _ H r F F' W₁ W₂ hμ hA hA' hW₁ hW₂
  obtain ⟨hW₁o, hW₁m, hW₁s⟩ := id hW₁
  obtain ⟨hW₂o, hW₂m, hW₂s⟩ := id hW₂
  have heF : ∀ a : Fin (r + 1), F.e a ∈ Formalism.HermitianLatticeCounting.S6.V0 F F' := by
    intro a
    induction a using Fin.lastCases with
    | last => exact lastVector_mem_jointSpan_left F F'
    | cast b => exact isotropicSpan_le_jointSpan_left F F' ((e_mem_X F) b)
  have heF' : ∀ a : Fin (r + 1), F'.e a ∈ Formalism.HermitianLatticeCounting.S6.V0 F F' := by
    intro a
    induction a using Fin.lastCases with
    | last => exact lastVector_mem_jointSpan_right F F'
    | cast b => exact isotropicSpan_le_jointSpan_right F F' ((e_mem_X F') b)
  have hanis : ∀ w ∈ W₁, H.B w w = 0 → w = 0 := by
    intro w hw hww
    have hwF : w ∈ F.X := hA w (fun a => hW₁o w hw _ (heF a)) hww
    have hwF' : w ∈ F'.X := hA' w (fun a => hW₁o w hw _ (heF' a)) hww
    have hmem : w ∈ W₁ ⊓ Formalism.HermitianLatticeCounting.S6.II F F' := Submodule.mem_inf.2 ⟨hw, Submodule.mem_inf.2 ⟨hwF, hwF'⟩⟩
    rw [hW₁m] at hmem
    exact (Submodule.mem_bot K).1 hmem
  let bm := Module.finBasis K (Formalism.HermitianLatticeCounting.S6.II F F')
  let b1 := Module.finBasis K W₁
  have hdec : ∀ k, ∃ m : Formalism.HermitianLatticeCounting.S6.II F F', (b1 k : V) - (m : V) ∈ W₂ := by
    intro k
    obtain ⟨w₂, hw₂, m, hm, hsum⟩ := Submodule.mem_sup.1 (hW₂s _ (hW₁o _ (b1 k).2))
    refine ⟨⟨m, hm⟩, ?_⟩
    rw [← hsum]
    simpa using hw₂
  choose mk hmk using hdec
  let φ : W₁ →ₗ[K] Formalism.HermitianLatticeCounting.S6.II F F' := b1.constr K mk
  have hφ : ∀ w : W₁, (w : V) - (φ w : V) ∈ W₂ := by
    intro w
    rw [← b1.sum_repr w]
    simp only [φ, map_sum, map_smul, Module.Basis.constr_basis, Submodule.coe_sum, Submodule.coe_smul]
    rw [← Finset.sum_sub_distrib]
    exact Submodule.sum_mem _ fun k _ => by
      rw [← smul_sub]
      exact Submodule.smul_mem _ _ (hmk k)
  have hv : ∀ i, ∃ v : V, v ∈ W₁ ∧ ∀ w : W₁, H.B (w : V) v = -(bm.repr (φ w) i) := by
    intro i
    obtain ⟨g, hg⟩ := LinearMap.exists_extend (-((bm.coord i).comp φ))
    obtain ⟨v, hvW, hvl⟩ := repr_aniso H W₁ hanis g
    refine ⟨v, hvW, fun w => ?_⟩
    rw [hvl w w.2]
    have h1 := LinearMap.congr_fun hg w
    simpa using h1
  choose v hvW hvB using hv
  obtain ⟨g, hg, hgw⟩ := good_family hE hR F F' hμ _ (fun i => (bm i : V)) v
    (fun i => (bm i).2) (fun i y hy => hW₁o _ (hvW i) y hy)
  obtain ⟨hU, hU'⟩ := Formalism.HermitianLatticeCounting.P.GoodMap.inN F F' hg
  obtain ⟨-, hbij, hfix, -⟩ := id hg
  refine ⟨g, hU, hU', hfix, ?_⟩
  have hle : W₁.map g ≤ W₂ := by
    rintro _ ⟨w, hw, rfl⟩
    rw [hgw w (hW₁o w hw)]
    have h2 : ∀ i, H.B w (v i) = -(bm.repr (φ ⟨w, hw⟩)) i := fun i => hvB i ⟨w, hw⟩
    have h3 : ∑ i, (bm.repr (φ ⟨w, hw⟩)) i • (bm i : V) = (φ ⟨w, hw⟩ : V) := by
      conv_rhs => rw [← bm.sum_repr (φ ⟨w, hw⟩)]
      simp only [Submodule.coe_sum, Submodule.coe_smul]
    simp only [h2, neg_smul, Finset.sum_neg_distrib]
    rw [h3, ← sub_eq_add_neg]
    exact hφ ⟨w, hw⟩
  have hsup : W₁ ⊔ Formalism.HermitianLatticeCounting.S6.II F F' = W₂ ⊔ Formalism.HermitianLatticeCounting.S6.II F F' :=
    le_antisymm (sup_le (fun w hw => hW₂s w (hW₁o w hw)) le_sup_right)
      (sup_le (fun w hw => hW₁s w (hW₂o w hw)) le_sup_right)
  have hfr : Module.finrank K W₁ = Module.finrank K W₂ := by
    have e1 := Submodule.finrank_sup_add_finrank_inf_eq W₁ (Formalism.HermitianLatticeCounting.S6.II F F')
    have e2 := Submodule.finrank_sup_add_finrank_inf_eq W₂ (Formalism.HermitianLatticeCounting.S6.II F F')
    rw [hW₁m, finrank_bot, hsup] at e1
    rw [hW₂m, finrank_bot] at e2
    omega
  exact Submodule.eq_of_le_of_finrank_eq hle
    (by rw [← (Submodule.equivMapOfInjective g hbij.1 W₁).finrank_eq, hfr])
end Formalism.HermitianLatticeCounting.P
