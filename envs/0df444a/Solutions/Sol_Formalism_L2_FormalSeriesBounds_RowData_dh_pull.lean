-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RowData.dh_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:08:47.790897+00:00
-- url     : https://prove2.me/submissions/90ca4a69-b56f-4b5f-bc85-6ed3cb2f2ec3

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_linS_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_linS_smul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_linS_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_dVar_subst_linS
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_toW_same
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_toW_other
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_hPullW_eq
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_row_upG_self
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_row_toLeaf
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_constantCoeff_ttPull
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_intGerm_pull
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_sum
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (Xr : RowData C V d I J) {ι ι' : Type} [Fintype ι]
  [Fintype ι']
namespace Formalism.L2.FormalSeriesBounds
namespace RowData
theorem _root_.solution (hAlt : Xr.Alt) (g : Fin 2) (a a' : ZMod d) (hodd : Odd (a' - a).val)
    (S : ∀ g, Sys (Xr.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C) (hT : ∀ g, (S g).IsT (t g))
    (e : ι → I g → C) (v' : ι' → I (1 - g) → C)
    (he : ∀ c x, (Xr.G g).ty (Sum.inl x) ≠ a → e c x = 0)
    (hv : ∀ b x, (Xr.G (1 - g)).ty (Sum.inl x) ≠ a' → v' b x = 0)
    (hvint : ∀ b x, V.Ge 0 (v' b x)) (b : ι') :
    ∃ Kp : MvPowerSeries (I g ⊕ I (1 - g)) C, (∀ A, V.Ge 0 (coeff A Kp)) ∧
      dVar (Sum.inr b)
          (hPullW (Xr.hL g a a') (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b))) =
        subst (ttPull t g e v') Kp +
          rename (Function.Embedding.inl : ι ↪ ι ⊕ ι')
            (∑ k : I (1 - g), v' b k • ∑ κ : J g,
              Xr.pair g κ k • subst (linS e) ((S g).ze (t g) κ)) := by
  have ht0 : ∀ g c, constantCoeff (t g c) = 0 := fun g c => (hT g).1 c
  have hs := hasSubst_of_constantCoeff_zero (constantCoeff_ttPull t ht0 g e v')

  have hk : ∀ k : I (1 - g), ∃ Kp : MvPowerSeries (I g ⊕ I (1 - g)) C,
      (∀ A, V.Ge 0 (coeff A Kp)) ∧
      v' b k • subst (linS (rowM g e v')) (dVar (⟨1 - g, k⟩ : WV I) (Xr.hL g a a')) =
        v' b k • (subst (ttPull t g e v') Kp +
          rename (Function.Embedding.inl : ι ↪ ι ⊕ ι')
            (∑ κ : J g, Xr.pair g κ k • subst (linS e) ((S g).ze (t g) κ))) := by
    intro k
    by_cases hkt : (Xr.G (1 - g)).ty (Sum.inl k) = a'
    · obtain ⟨K, hK, hEq⟩ := Xr.C_eq hAlt g a a' hodd S t hT k hkt
      obtain ⟨Kp, hKp, hKpe⟩ := intGerm_pull V t ht0 g e v' hK
      refine ⟨Kp, hKp, ?_⟩
      congr 1
      have h1 : dVar (⟨1 - g, k⟩ : WV I) (Xr.hL g a a') =
          toLeaf Xr.G g a a' K +
            toLeaf Xr.G g a a' (∑ κ : J g, Xr.pair g κ k • upG g ((S g).ze (t g) κ)) := by
        rw [← hEq]; ring
      rw [h1, subst_linS_add, subst_row_toLeaf Xr.G g a a' e v' he hv,
        subst_row_toLeaf Xr.G g a a' e v' he hv, hKpe, subst_linS_sum, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun κ _ => ?_
      rw [subst_linS_smul, subst_row_upG_self, map_smul]
    · exact ⟨0, fun A => by simpa using VF.Ge.zero (V := V) 0, by rw [hv b k hkt, zero_smul, zero_smul]⟩
  choose Kp hKp hKpe using hk
  refine ⟨∑ k, v' b k • Kp k, ?_, ?_⟩
  · intro A
    rw [map_sum]
    refine VF.Ge.sum fun k _ => ?_
    rw [map_smul, smul_eq_mul]
    exact (hvint b k).mul_int (hKp k A)
  · rw [hPullW_eq, dVar_subst_linS]
    have hsig : ∑ w : WV I, rowM g e v' (Sum.inr b) w •
          subst (linS (rowM g e v')) (dVar w (Xr.hL g a a')) =
        ∑ k : I (1 - g), v' b k •
          subst (linS (rowM g e v')) (dVar (⟨1 - g, k⟩ : WV I) (Xr.hL g a a')) := by
      rw [Fintype.sum_sigma, Finset.sum_eq_single (1 - g)]
      · refine Finset.sum_congr rfl fun k _ => ?_
        show toW (1 - g) (v' b) _ • _ = _
        rw [toW_same]
      · intro g' _ hg'
        refine Finset.sum_eq_zero fun x _ => ?_
        show toW (1 - g) (v' b) _ • _ = _
        rw [toW_other _ _ hg', zero_smul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsig]
    simp only [hKpe, smul_add]
    rw [Finset.sum_add_distrib, map_sum]
    congr 1
    · rw [← substAlgHom_apply hs, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, substAlgHom_apply]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul]
end RowData
end Formalism.L2.FormalSeriesBounds
