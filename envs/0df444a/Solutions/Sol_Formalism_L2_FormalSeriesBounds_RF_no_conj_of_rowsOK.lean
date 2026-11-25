-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.no_conj_of_rowsOK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:49:15.495809+00:00
-- url     : https://prove2.me/submissions/8915894f-4e9c-428b-ad19-821310258275

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FinTwoNeOneSub

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
open Formalism.IncomingBounds Formalism.L2.Pj
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution {G : ∀ g, Cart V d (I g) (J g)} {alt : Prop} {N : ℕ} {P : MvPolynomial (Fin N × WV I) C}
    {kind : Fin N → Knd d} (h : RowsOK G alt P kind) {ρ : Fin N} {w w' : WV I} (hw : (ρ, w) ∈ P.vars)
    (hw' : (ρ, w') ∈ P.vars) (hg : w.1 ≠ w'.1) (ht : tyW G w = tyW G w') : False := by
  obtain ⟨h1, h2⟩ := h
  rw [MvPolynomial.mem_vars] at hw hw'
  obtain ⟨μ, hμ, hμw⟩ := hw
  obtain ⟨μ', hμ', hμw'⟩ := hw'
  rcases hk : kind ρ with _ | ⟨g, a, a'⟩
  · obtain ⟨g, hg'⟩ := h2 ρ hk
    have e1 := hg' μ hμ w (Finsupp.mem_support_iff.1 hμw)
    have e2 := hg' μ' hμ' w' (Finsupp.mem_support_iff.1 hμw')
    exact hg (e1.trans e2.symm)
  · obtain ⟨-, hodd, hleaf⟩ := h1 ρ g a a' hk
    have l1 := hleaf μ hμ w (Finsupp.mem_support_iff.1 hμw)
    have l2 := hleaf μ' hμ' w' (Finsupp.mem_support_iff.1 hμw')
    rcases l1 with ⟨e1, t1⟩ | ⟨e1, t1⟩ <;> rcases l2 with ⟨e2, t2⟩ | ⟨e2, t2⟩
    · exact hg (e1.trans e2.symm)
    · have he : a = a' := t1.symm.trans (ht.trans t2)
      rw [he, sub_self, ZMod.val_zero] at hodd
      exact absurd hodd (by decide)
    · have he : a' = a := t1.symm.trans (ht.trans t2)
      rw [he, sub_self, ZMod.val_zero] at hodd
      exact absurd hodd (by decide)
    · exact hg (e1.trans e2.symm)
end Formalism.L2.FormalSeriesBounds.RF
