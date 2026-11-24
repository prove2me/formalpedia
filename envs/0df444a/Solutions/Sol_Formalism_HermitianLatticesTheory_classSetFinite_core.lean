-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.classSetFinite_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:58:48.714875+00:00
-- url     : https://prove2.me/submissions/e67dbaa8-a22a-486d-aa24-aef51fcf4d5b

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_mem_zmap
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_min
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (hC : ShortVectors) (hE : FinIntermediate) (hF : IsomOfTrace)
    {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (n : ℕ) (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (hmul : ∀ a : K, ∃ C : ℝ, ∀ x : V, ‖ι (a • x)‖ ≤ C * ‖ι x‖)
    (d : ℕ) (hd : 0 < d) (C : ℝ) (S : Set (Submodule (NumberField.RingOfIntegers K) V))
    (hSd : ∀ M ∈ S, ∀ x ∈ M, ∀ y ∈ M,
      (d : K) * h x y ∈ (1 : Submodule (NumberField.RingOfIntegers K) K))
    (hSlat : ∀ M ∈ S, ∃ _ : DiscreteTopology (zmap ι M), IsZLattice ℝ (zmap ι M))
    (hSC : ∀ M ∈ S, ∀ [DiscreteTopology (zmap ι M)] [IsZLattice ℝ (zmap ι M)],
      ZLattice.covolume (zmap ι M) ≤ C) :
    ∃ s : Finset (Submodule (NumberField.RingOfIntegers K) V), (∀ N ∈ s, N ∈ S) ∧
      ∀ M ∈ S, ∃ N ∈ s, ∃ g ∈ isom h, gmap g N = M := by
  unfold ShortVectors at hC
  have hdR : (0 : ℝ) < 1 / (d : ℝ) := one_div_pos.mpr (by exact_mod_cast hd)
  obtain ⟨B, hB⟩ := hC n (1 / (d : ℝ)) C hdR
  refine classSetAssembly_main hE hF h hpos ι hι hmul d hd S hSd B ?_
  intro M hM
  obtain ⟨hdisc, hlat⟩ := hSlat M hM
  have := hdisc
  have := hlat
  obtain ⟨v, hvmem, hvli, hvB⟩ := hB (zmap ι M) (fun w hw hw0 => by
      obtain ⟨x, hx, rfl⟩ := (classSetAssembly_mem_zmap ι M w).mp hw
      have hx0 : x ≠ 0 := by
        rintro rfl
        exact hw0 (map_zero ι)
      exact classSetAssembly_min h hpos ι hι d hd M (hSd M hM) x hx hx0)
    (hSC M hM)
  choose x hx using fun i => (classSetAssembly_mem_zmap ι M (v i)).mp (hvmem i)
  have hxv : ι ∘ x = v := funext fun i => (hx i).2
  refine ⟨x, fun i => (hx i).1, ?_, fun i => ?_⟩
  · rw [hxv]
    exact hvli
  · rw [(hx i).2]
    exact hvB i
end Formalism.HermitianLatticesTheory
