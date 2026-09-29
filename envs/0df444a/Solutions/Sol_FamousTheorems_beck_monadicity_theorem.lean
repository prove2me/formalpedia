-- Prove2me | solution 1 for FamousTheorems.beck_monadicity_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:12:51.499356+00:00
-- url     : https://prove2.me/submissions/8522ea73-f0d3-4d25-801e-11290fa7d482

import Mathlib

universe v

theorem solution {C D : Type*} [CategoryTheory.Category.{v} C] [CategoryTheory.Category.{v} D]
    {G : CategoryTheory.Functor D C} {F : CategoryTheory.Functor C D} (adj : CategoryTheory.Adjunction F G)
    [G.ReflectsIsomorphisms] [CategoryTheory.Monad.HasCoequalizerOfIsSplitPair G]
    [CategoryTheory.Monad.PreservesColimitOfIsSplitPair G] : Nonempty (CategoryTheory.MonadicRightAdjoint G) :=
  ⟨CategoryTheory.Monad.monadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorphisms adj⟩
