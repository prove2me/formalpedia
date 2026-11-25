-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.rtj_antidiag_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:34:26.022952+00:00
-- url     : https://prove2.me/submissions/9572e17a-a43f-4e2b-a0da-b8547ab1e732

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_split_unique

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
theorem _root_.solution {A : Set σ} (f g : (σ →₀ ℕ) → K)
    (hf : ∀ c, f c ≠ 0 → (↑c.support : Set σ) ⊆ A)
    (hg : ∀ d, g d ≠ 0 → (↑d.support : Set σ) ⊆ Aᶜ)
    {a b : σ →₀ ℕ} (ha : (↑a.support : Set σ) ⊆ A) (hb : (↑b.support : Set σ) ⊆ Aᶜ) :
    ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b), f x.1 * g x.2 = f a * g b := by
  rw [Finset.sum_eq_single_of_mem (a, b) (Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl)]
  intro x hx hne
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  by_contra h0
  have hfc : f x.1 ≠ 0 := left_ne_zero_of_mul h0
  have hgd : g x.2 ≠ 0 := right_ne_zero_of_mul h0
  obtain ⟨h1, h2⟩ := rtj_split_unique ha hb (hf x.1 hfc) (hg x.2 hgd) hx
  exact hne (Prod.ext h1 h2)
end Formalism.L2.FormalSeriesBounds
