-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x7.admitted.pow_bdd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:43.054895+00:00
-- url     : https://prove2.me/submissions/3c7fd716-f7aa-4cc8-acfe-a8c867706ad8

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_small
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_isLat_mulR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x7 Formalism.FourierDecayAlt.P.A6x7.admitted
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A6x7.admitted
theorem _root_.solution (hD : LocalDatum K R ψ) (h0 : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) {ϖ : Kˣ}
    (hϖ : (ϖ : K) ∈ R) (hϖ' : ∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R) (s : ℕ) (hs : 1 ≤ s) :
    ∃ N : ℕ, ∀ w : K, w ^ s ∈ R → (ϖ : K) ^ N * w ∈ R := by
  classical
  have := hD.t2
  have := hD.red
  have hC : IsCompact ((R : Set K) \ (mulR R (ϖ : K) : Set K)) :=
    hD.isCompact.diff (isLat_mulR hD ϖ).1
  have hcl : IsClosed ((fun v : K => v ^ s) '' ((R : Set K) \ (mulR R (ϖ : K) : Set K))) :=
    (hC.image (continuous_pow s)).isClosed
  have h0n : (0 : K) ∉ (fun v : K => v ^ s) '' ((R : Set K) \ (mulR R (ϖ : K) : Set K)) := by
    rintro ⟨v, hv, hv0⟩
    have : v = 0 := IsReduced.eq_zero v ⟨s, hv0⟩
    exact hv.2 (this ▸ (mulR R (ϖ : K)).zero_mem)
  obtain ⟨N, hN⟩ := small hD h0 hϖ hϖ' _ (hcl.isOpen_compl.mem_nhds h0n)
  refine ⟨N, fun w hw => ?_⟩
  have hn := Nat.find_spec (hϖ' w)
  have hmin := fun k => Nat.find_min (hϖ' w) (m := k)
  set n := Nat.find (hϖ' w) with hn_def
  by_cases hle : n ≤ N
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    have e : (ϖ : K) ^ N * w = (ϖ : K) ^ k * ((ϖ : K) ^ n * w) := by rw [hk, pow_add]; ring
    rw [e]; exact R.mul_mem (R.pow_mem hϖ k) hn
  · exfalso
    have hn1 : n = (n - 1) + 1 := by omega
    have hv : (ϖ : K) ^ n * w ∈ (R : Set K) \ (mulR R (ϖ : K) : Set K) := by
      refine ⟨hn, ?_⟩
      rintro ⟨r, hr, hr'⟩
      apply hmin (n - 1) (by omega)
      have hr2 : (ϖ : K) * r = (ϖ : K) ^ n * w := hr'
      have e : (ϖ : K) ^ (n - 1) * w = r := by
        apply ϖ.isUnit.mul_left_cancel
        rw [hr2, hn1, Nat.add_sub_cancel, pow_succ]; ring
      rw [e]; exact hr
    obtain ⟨k, hk⟩ : ∃ k, n * s = N + k := Nat.exists_eq_add_of_le (by nlinarith)
    apply hN ((ϖ : K) ^ k * w ^ s) (R.mul_mem (R.pow_mem hϖ k) hw)
    refine ⟨_, hv, ?_⟩
    show ((ϖ : K) ^ n * w) ^ s = (ϖ : K) ^ N * ((ϖ : K) ^ k * w ^ s)
    rw [mul_pow, ← pow_mul, hk, pow_add]; ring
end Formalism.FourierDecayAlt.P.A6x7.admitted
