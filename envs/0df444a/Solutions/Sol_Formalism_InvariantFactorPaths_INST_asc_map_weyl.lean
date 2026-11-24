-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.INST.asc_map_weyl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:51.566269+00:00
-- url     : https://prove2.me/submissions/a3138beb-d905-4de7-b128-45626ff2a101

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_Ascent
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.ext_castSucc
attribute [local simp] Formalism.GM.M.FB.ext_last
attribute [local simp] Formalism.GM.M.FB.res_apply
attribute [local simp] Formalism.GM.M.FB.res_ext
attribute [local simp] Formalism.GM.M.FB.snoc_deg_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_deg_last
attribute [local simp] Formalism.GM.M.FB.snoc_vec_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_vec_last
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.INST
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.INST
theorem _root_.solution (O : Type) [CommRing O] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (f : MvPolynomial (Fin r × Fin n) ℤ) (hf : f ∈ weyl ℤ r n hn ν) :
    map (Int.castRingHom O) f ∈ weyl O r n hn ν := by
  set φ : ℤ →+* O := Int.castRingHom O with hφ
  have hrow : ∀ (a b : Fin r) (g : MvPolynomial (Fin r × Fin n) ℤ),
      rowGen O a b (map φ g) = Polynomial.map (map φ) (rowGen ℤ a b g) := by
    intro a b g
    have key : ((rowGen O a b).toRingHom.comp (map φ) :
          MvPolynomial (Fin r × Fin n) ℤ →+* Polynomial (MvPolynomial (Fin r × Fin n) O)) =
        (Polynomial.mapRingHom (map φ)).comp (rowGen ℤ a b).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro c
        rw [← RingHom.comp_apply, eq_intCast, ← RingHom.comp_apply, eq_intCast]
      · intro v
        simp only [RingHom.comp_apply]
        (simp [rowGen]) <;> (try split_ifs) <;> (try simp)
    exact RingHom.congr_fun key g
  have hdiv : ∀ (a b : Fin r) (k : ℕ) (g : MvPolynomial (Fin r × Fin n) ℤ),
      map φ (rowDiv ℤ a b k g) = rowDiv O a b k (map φ g) := by
    intro a b k g
    unfold rowDiv
    rw [hrow, Polynomial.coeff_map]
  have hword : ∀ (w : List (Fin r × Fin r × ℕ)) (g : MvPolynomial (Fin r × Fin n) ℤ),
      map φ (applyWord ℤ w g) = applyWord O w (map φ g) := by
    intro w g
    induction w with
    | nil => rfl
    | cons x w ih =>
      show map φ (rowDiv ℤ x.1 x.2.1 x.2.2 (applyWord ℤ w g)) =
        rowDiv O x.1 x.2.1 x.2.2 (applyWord O w (map φ g))
      rw [hdiv, ih]
  have hhw : map φ (hw ℤ hn ν) = hw O hn ν := by
    unfold hw
    rw [map_prod]
    refine Finset.prod_congr rfl (fun s _ => ?_)
    rw [map_pow]
    congr 1
    unfold lpMinor
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [RingHom.mapMatrix_apply, Matrix.map_apply]
  unfold weyl at hf ⊢
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    refine Submodule.subset_span ⟨w, ?_⟩
    try dsimp only
    rw [hword, hhw]
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [map_zsmul]
    first
      | exact zsmul_mem hx c
      | exact Submodule.smul_of_tower_mem _ c hx
end Formalism.InvariantFactorPaths.INST
