-- Prove2me | solution 1 for EdenVerified.D10_kaplan_yorke_convention
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:02:20.862443+00:00
-- url     : https://prove2.me/submissions/0009de80-b633-4de7-98c1-41fde490fbc0

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_kaplanYorkeDimension_mem_interval
import Theorems.Thm_Eden_kaplanYorkeDimension_of_index_between
import Theorems.Thm_Eden_kaplanYorkeDimension_of_index_five
import Theorems.Thm_Eden_kaplanYorkeDimension_of_index_zero
import Theorems.Thm_Eden_kaplanYorkeIndex_mem
import Theorems.Thm_Eden_le_kaplanYorkeIndex
import Theorems.Thm_Eden_spectrumEntry_at_kaplanYorkeIndex_neg


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (a : Fin 5 → ℝ) :
    spectrumPartialSum a 0 = 0 ∧
    kaplanYorkeDimension a ∈ Icc 0 5 ∧
    (∀ k : ℕ, spectrumPartialSum a k = ∑ i ∈ Finset.range k, spectrumEntry a i) ∧
    (kaplanYorkeIndex a ≤ 5 ∧ 0 ≤ spectrumPartialSum a (kaplanYorkeIndex a)) ∧
    (∀ k : ℕ, k ≤ 5 → 0 ≤ spectrumPartialSum a k → k ≤ kaplanYorkeIndex a) ∧
    (kaplanYorkeIndex a = 0 → kaplanYorkeDimension a = 0) ∧
    (kaplanYorkeIndex a = 5 → kaplanYorkeDimension a = 5) ∧
    (0 < kaplanYorkeIndex a → kaplanYorkeIndex a < 5 →
      spectrumEntry a (kaplanYorkeIndex a) < 0 ∧
      kaplanYorkeDimension a = (kaplanYorkeIndex a : ℝ) +
        spectrumPartialSum a (kaplanYorkeIndex a) / |spectrumEntry a (kaplanYorkeIndex a)|) :=
  ⟨spectrumPartialSum_zero a, kaplanYorkeDimension_mem_interval a,
    fun _ => rfl, kaplanYorkeIndex_mem a,
    fun _k hk hs => le_kaplanYorkeIndex hk hs, kaplanYorkeDimension_of_index_zero,
    kaplanYorkeDimension_of_index_five, fun h₀ h₅ =>
      ⟨spectrumEntry_at_kaplanYorkeIndex_neg h₅,
        kaplanYorkeDimension_of_index_between rfl h₀ h₅⟩⟩
end EdenVerified
