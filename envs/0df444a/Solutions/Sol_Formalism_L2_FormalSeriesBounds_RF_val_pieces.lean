-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.val_pieces
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:51:24.161253+00:00
-- url     : https://prove2.me/submissions/6a3468b3-4b03-4448-be31-ff50742387b8

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ContentZeroAt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_v_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_exists_sys_isT
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_one_mem_intGerm
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_plAt_inj
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rowsOK_prodAll


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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
  (X : ∀ o, RowData C V d (I o) (J o)) (n : ℕ)
variable {X n}
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution {FFimg : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)} {ν : ℝ} (hV : ValO X n FFimg ν) (hJ : JetProdSt)
    (K : Orb → ℕ) (what₂ : ∀ o, Fin (K o) → ℕ) (pl : (Σ o, Σ i : Fin (K o), Fin (what₂ o i)) → Fin n)
    (hpl : Function.Injective pl)
    (Pc : ∀ o i, MvPolynomial (Fin (what₂ o i) × WV (I o)) C) (kind : ∀ o i, Fin (what₂ o i) → Knd d)
    (c : ∀ o, Fin (K o) → ℝ)
    (hrow : ∀ o i, RowsOK (X o).G (X o).Alt (Pc o i) (kind o i))
    (hatt : ∀ o i, ∃ (S : ∀ g, Sys ((X o).G g)) (t : ∀ g, I o g → MvPowerSeries (I o g) C),
      (∀ g, (S g).IsT (t g)) ∧ ∃ gr : Fin (what₂ o i) → MvPowerSeries (WV (I o)) C, (∀ ρ, gr ρ ∈ IntGerm V t) ∧
        V.v (ValOf (X o).hL (Pc o i) (kind o i) gr) ≤ ((c o i : ℝ) : WithTop ℝ))
    (hmem : (fun o => prodAll (plAt n pl o) (Pc o)) ∈ FFimg) :
    ν ≤ ∑ o, ∑ i, c o i := by
  choose S₁ t₁ ht₁ gr₁ hg₁ hc₁ using hatt
  have hsys : ∀ o g, ∃ (S : Sys ((X o).G g)) (t : I o g → MvPowerSeries (I o g) C), S.IsT t :=
    fun o g => exists_sys_isT _
  choose S₀ t₀ ht₀ using hsys
  have hG : ∀ o i, IntGerm V (t₁ o i) = IntGerm V (t₀ o) :=
    fun o i => (X o).G0 (S₁ o i) (S₀ o) (t₁ o i) (t₀ o) (ht₁ o i) (ht₀ o)
  have hgr : ∀ o ρ, grAll (plAt n pl o) (gr₁ o) ρ ∈ IntGerm V (t₀ o) := by
    intro o ρ
    unfold grAll
    split_ifs with h
    · rw [← hG o h.choose.1]
      exact hg₁ o _ _
    · exact one_mem_intGerm _
  have h1 := hV _ hmem (fun o => kindAll (plAt n pl o) (kind o))
    (fun o => rowsOK_prodAll _ _ (plAt_inj n hpl o) _ _ (hrow o)) S₀ t₀ ht₀
    (fun o => grAll (plAt n pl o) (gr₁ o)) hgr
  have h2 : ∑ o, V.v (ValOf (X o).hL (prodAll (plAt n pl o) (Pc o)) (kindAll (plAt n pl o) (kind o))
      (grAll (plAt n pl o) (gr₁ o))) = ∑ o, ∑ i, V.v (ValOf (X o).hL (Pc o i) (kind o i) (gr₁ o i)) := by
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [hJ C d (I o) _ n (K o) (what₂ o) (plAt n pl o) (plAt_inj n hpl o) (Pc o) (kind o) (gr₁ o), v_prod]
  have h3 : (ν : WithTop ℝ) ≤ ((∑ o, ∑ i, c o i : ℝ) : WithTop ℝ) := by
    rw [h2] at h1
    refine h1.trans ?_
    push_cast
    exact Finset.sum_le_sum fun o _ => Finset.sum_le_sum fun i _ => hc₁ o i
  exact_mod_cast h3
end Formalism.L2.FormalSeriesBounds.RF
