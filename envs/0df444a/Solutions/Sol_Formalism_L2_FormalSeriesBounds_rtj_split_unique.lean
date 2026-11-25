-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.rtj_split_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:26:34.656049+00:00
-- url     : https://prove2.me/submissions/e204f491-cd2f-4896-8bd4-e0a3d368bdb7

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet

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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {K : Type} [Field K] {σ : Type}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {A : Set σ} {a b c d : σ →₀ ℕ} (ha : (↑a.support : Set σ) ⊆ A)
    (hb : (↑b.support : Set σ) ⊆ Aᶜ) (hc : (↑c.support : Set σ) ⊆ A)
    (hd : (↑d.support : Set σ) ⊆ Aᶜ) (h : c + d = a + b) : c = a ∧ d = b := by
  have key : ∀ i, c i = a i ∧ d i = b i := by
    intro i
    have hi : c i + d i = a i + b i := by
      have := congrArg (fun f : σ →₀ ℕ => f i) h
      simpa only [Finsupp.add_apply] using this
    by_cases hA : i ∈ A
    · have hb0 : b i = 0 := by
        by_contra hne
        exact hb (Finsupp.mem_support_iff.mpr hne) hA
      have hd0 : d i = 0 := by
        by_contra hne
        exact hd (Finsupp.mem_support_iff.mpr hne) hA
      omega
    · have ha0 : a i = 0 := by
        by_contra hne
        exact hA (ha (Finsupp.mem_support_iff.mpr hne))
      have hc0 : c i = 0 := by
        by_contra hne
        exact hA (hc (Finsupp.mem_support_iff.mpr hne))
      omega
  exact ⟨Finsupp.ext fun i => (key i).1, Finsupp.ext fun i => (key i).2⟩
end Formalism.L2.FormalSeriesBounds
