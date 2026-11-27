-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.tyS_good_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:48:32.824155+00:00
-- url     : https://prove2.me/submissions/30282f7a-2e63-4de3-8c92-b5d8444c239a

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RankMaximalOfNondegenerate
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Agr_symm
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h3
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {g : Fin 2} {w : I g → C} {x : ℕ → I g ⊕ JJ I g → C}
    (h0 : x 0 = Sum.elim w 0) (h1 : ∀ c, x 1 (Sum.inl c) = 0) (hl : 2 ≤ V.l) (c : I g) (n : ℕ)
    (hn : n < V.l ^ 2) :
    PowerSeries.coeff n (tyS V.l (fun s => x s (Sum.inl c))) = if n = 1 then w c else 0 := by
  unfold tyS
  rw [PowerSeries.coeff_mk, Finset.sum_eq_single 0]
  · rw [pow_zero]
    by_cases hn1 : n = 1
    · subst hn1
      rw [if_pos rfl, if_pos rfl]
      simp [h0]
    · have hn1' : ¬ (1 = n) := fun h => hn1 h.symm
      rw [if_neg hn1', if_neg hn1]
  · intro s _ hs0
    by_cases hs1 : s = 1
    · subst hs1
      simp [h1 c]
    · rw [if_neg]
      intro hsn
      have h2 : 2 ≤ s := by omega
      have h3 : V.l ^ 2 ≤ V.l ^ s := Nat.pow_le_pow_right (by omega) h2
      rw [hsn] at h3
      exact absurd hn (not_lt.mpr h3)
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.succ_pos n)) h
end Formalism.L2.FormalSeriesBounds
