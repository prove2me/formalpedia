-- Prove2me | solution 1 for Erdos919.e918_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:39:46.77636+00:00
-- url     : https://prove2.me/submissions/5f57639c-0c0c-4056-9155-fe8c20735916

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_mk_W
public import Theorems.Thm_Erdos919_chromaticCardinal_eq_aleph2_iff
public import Theorems.Thm_Erdos919_chromaticCardinal_comap_equiv
public import Theorems.Thm_Erdos919_size_iff

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution :
    (∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ G.chromaticCardinal = ℵ_ 2 ∧
      ∀ (W : Set V) (_ : #W = ℵ₁), (G.induce W).chromaticCardinal ≤ ℵ₀) ↔
    ∃ H : SimpleGraph W.{u}, SmallCardCC H ∧ ChiAleph2 H := by
  rw [size_iff (fun G => G.chromaticCardinal = ℵ_ 2)
    (fun e G => by rw [chromaticCardinal_comap_equiv])]
  refine exists_congr fun H => ?_
  rw [chromaticCardinal_eq_aleph2_iff H mk_W]
end Erdos919
