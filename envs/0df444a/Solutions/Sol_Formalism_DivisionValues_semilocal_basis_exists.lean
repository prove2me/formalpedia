-- Prove2me | solution 1 for Formalism.DivisionValues.semilocal_basis_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:57:23.136796+00:00
-- url     : https://prove2.me/submissions/a02c9e64-ed3e-4ad7-9cf6-faa10631d9c4

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Theorems.Thm_Formalism_DivisionValues_SemilocalBasisHermitianTwistDivisors_primes_finite
import Theorems.Thm_Formalism_DivisionValues_SemilocalBasisHermitianTwistDivisors_mem_loc_iff_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.DivisionValues
open SemilocalBasisHermitianTwistDivisors
namespace Formalism.DivisionValues
theorem _root_.solution : LocBasisEx := by
  intro K _ _ _ d L hL w
  have : IsDedekindDomain (A w) :=
    IsLocalization.isDedekindDomain (𝓞 K) (hcompl_le w) (A w)
  have : IsPrincipalIdealRing (A w) := IsPrincipalIdealRing.of_finite_primes (primes_finite w)
  set N : Submodule (A w) (Fin d → K) := Submodule.span (A w) (L : Set (Fin d → K)) with hN
  have : Module.Finite (A w) N := by
    obtain ⟨s, hs⟩ := hL.fg
    rw [Module.Finite.iff_fg]
    refine ⟨s, ?_⟩
    rw [hN, ← hs, Submodule.span_span_of_tower]
  have : Module.IsTorsionFree (A w) N := inferInstance
  let b := Module.Free.chooseBasis (A w) N
  let v : Module.Free.ChooseBasisIndex (A w) N → Fin d → K := fun i => (b i : Fin d → K)
  have hliA : LinearIndependent (A w) v := b.linearIndependent.map' N.subtype N.ker_subtype
  have hli : LinearIndependent K v := (LinearIndependent.iff_fractionRing (A w) K).mp hliA
  have hspanA : Submodule.span (A w) (Set.range v) = N := by
    have : Set.range v = N.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspan : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← hL.span_eq_top, Submodule.span_le]
    intro x hx
    have hxN : x ∈ Submodule.span (A w) (Set.range v) := by
      rw [hspanA]; exact Submodule.subset_span hx
    exact Submodule.span_le_restrictScalars (A w) K _ hxN
  let bK : Basis _ K (Fin d → K) := Basis.mk hli hspan
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex (A w) N) = d := by
    rw [← Module.finrank_eq_card_basis bK, Module.finrank_fin_fun]
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨v ∘ e.symm, hli.comp _ e.symm.injective, ?_⟩
  ext x
  rw [mem_loc_iff_span, mem_loc_iff_span, Submodule.span_span_of_tower, EquivLike.range_comp,
    hspanA]
end Formalism.DivisionValues
