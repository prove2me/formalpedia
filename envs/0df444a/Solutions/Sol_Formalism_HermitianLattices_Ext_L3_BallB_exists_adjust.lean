-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BallB.exists_adjust
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:29.865916+00:00
-- url     : https://prove2.me/submissions/2f3c1938-f073-481b-b648-5face8a938da

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemConjIdeal
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormDiscrIdealOfLe
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BallB
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.BallB
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {c : 𝓞 K}
    (hc : c ∉ P) : ∃ π ∈ P, c + π ∉ P ∧ c + π ∉ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
  have hadd : ∀ π ∈ P, c + π ∉ P := fun π hπ h => hc (by simpa using P.sub_mem h hπ)
  have hle2 : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≤ P.comap (conjO K) := by
    refine Ideal.span_le.2 ?_
    rintro r ⟨s, hs, hrs⟩
    show conjO K r ∈ P
    have e : conjO K r = s := by
      apply IsFractionRing.injective (𝓞 K) K
      have e1 : algebraMap (𝓞 K) K (conjO K r) = star (algebraMap (𝓞 K) K r) := by
        first | rfl | simp [conjO]
      rw [e1, hrs, star_star]
    rw [e]
    exact hs
  have hne_top : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ ⊤ := by
    intro htop
    have h1 : (1 : 𝓞 K) ∈ P.comap (conjO K) := hle2 (by rw [htop]; exact Submodule.mem_top)
    rw [Ideal.mem_comap, map_one] at h1
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 h1)
  by_cases hc' : c ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P
  · have hnle : ¬ P ≤ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
      intro hle
      have hPe := hP.eq_of_le hne_top hle
      exact hc (by rw [hPe]; exact hc')
    obtain ⟨π, hπ, hπ'⟩ := SetLike.not_le_iff_exists.1 hnle
    refine ⟨π, hπ, hadd π hπ, fun h => hπ' ?_⟩
    have h3 := (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P).sub_mem h hc'
    simpa using h3
  · exact ⟨0, P.zero_mem, by simpa using hc, by simpa using hc'⟩
end Formalism.HermitianLattices.Ext.L3.BallB
