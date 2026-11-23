-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.exists_near
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:15.980275+00:00
-- url     : https://prove2.me/submissions/605b77fb-cb78-48a2-bfb7-c51486dd3bf1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_AdeleIntA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]
private theorem memO_lemma (v : HeightOneSpectrum R) (x : v.adicCompletion K) :
    x ∈ v.adicCompletionIntegers K ↔ Valued.v x ≤ 1 := by
  first
  | exact IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers ..
  | exact Iff.rfl
  | exact Valuation.mem_valuationSubring_iff _ _
  | simp [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]
namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA
theorem _root_.solution (v : HeightOneSpectrum R) (y : v.adicCompletion K) :
    ∃ k : K, y - algebraMap K (v.adicCompletion K) k ∈ v.adicCompletionIntegers K := by
  have hd : ∀ y : v.adicCompletion K, y ∈ closure (Set.range (algebraMap K (v.adicCompletion K))) := by
    first
    | exact fun y => UniformSpace.Completion.denseRange_coe y
    | exact UniformSpace.Completion.denseRange_coe
    | (intro y; exact (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := R) K v) y)
    | (intro y; exact (Valuation.Completion.denseRange_coe (v.valuation K)) y)
    | (unfold IsDedekindDomain.HeightOneSpectrum.adicCompletion Valuation.Completion;
        exact UniformSpace.Completion.denseRange_coe)
    | (unfold IsDedekindDomain.HeightOneSpectrum.adicCompletion;
        exact UniformSpace.Completion.denseRange_coe)
    | (delta IsDedekindDomain.HeightOneSpectrum.adicCompletion;
        exact UniformSpace.Completion.denseRange_coe)
  have hN : {z : v.adicCompletion K | Valued.v (z - y) < 1} ∈ nhds y := by
    first
    | exact Valued.mem_nhds.2 ⟨1, fun z hz => by simpa using hz⟩
    | (rw [Valued.mem_nhds]; exact ⟨1, fun z hz => by simpa using hz⟩)
    | exact (Valued.mem_nhds (x := y)).2 ⟨1, fun z hz => by simpa using hz⟩
  obtain ⟨_, hz, k, rfl⟩ := mem_closure_iff_nhds.1 (hd y) _ hN
  have hz' : Valued.v (algebraMap K (v.adicCompletion K) k - y) < 1 := hz
  refine ⟨k, (memO_lemma v _).2 ?_⟩
  first
  | (rw [Valuation.map_sub_swap]; exact le_of_lt hz')
  | (rw [← neg_sub, Valuation.map_neg]; exact le_of_lt hz')
end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA
