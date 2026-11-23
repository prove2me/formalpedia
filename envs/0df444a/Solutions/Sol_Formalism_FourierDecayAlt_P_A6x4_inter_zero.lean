-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x4.inter_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:10.771296+00:00
-- url     : https://prove2.me/submissions/d8b4bc32-e4cf-4419-a657-e704d08feca0

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_pow_mul_pow_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_vnr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x4
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A6x4
theorem _root_.solution (hD : LocalDatum K R ψ) (hQ : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) {p q : K}
    (hpq : p * q = 1) (hex : ∀ x : K, ∃ m : ℕ, p ^ m * x ∈ R) {z : K}
    (hz : ∀ m : ℕ, q ^ m * z ∈ R) : z = 0 := by
  have := hD.t2
  have := hD.artin
  have := hD.red
  by_contra hz0
  set J : Set K := {x | ∀ m : ℕ, q ^ m * x ∈ R} with hJ
  have hJmul : ∀ c x, x ∈ J → c * x ∈ J := by
    intro c x hx m
    obtain ⟨k, hk⟩ := hex c
    have h2 := R.mul_mem hk (hx (m + k))
    have e : q ^ m * (c * x) = p ^ k * c * (q ^ (m + k) * x) := by
      have h1 : p ^ k * q ^ k = 1 := pow_mul_pow_one hpq k
      rw [pow_add]
      linear_combination (-(q ^ m * c * x)) * h1
    rw [e]
    exact h2
  have hJc : IsCompact J := by
    apply hD.isCompact.of_isClosed_subset
    · have : J = ⋂ m : ℕ, (fun x => q ^ m * x) ⁻¹' (R : Set K) := by
        ext x
        simp [hJ]
      rw [this]
      exact isClosed_iInter fun m => hD.isCompact.isClosed.preimage (by fun_prop)
    · intro x hx
      simpa using hx 0
  have hopen : IsOpen {ab : K × K | ab.1 * ab.2 ≠ z} :=
    (isOpen_compl_singleton (x := z)).preimage (continuous_fst.mul continuous_snd)
  obtain ⟨U, V, hU, hV, h0U, hJV, hUV⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := (0 : K))) hJc hopen (by
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      have ha' : a = 0 := ha
      subst ha'
      show (0 : K) * b ≠ z
      rw [zero_mul]
      exact Ne.symm hz0)
  have hzJ : z ∈ J := hz
  have hseq : ∀ n : ℕ, (n : K) * z ∈ J := fun n => hJmul _ _ hzJ
  obtain ⟨a, haJ, ha⟩ := hJc.exists_clusterPt (f := map (fun n : ℕ => (n : K) * z) atTop) (by
    rw [le_principal_iff]
    exact mem_map.2 (univ_mem' hseq))
  have hU0 : U ∈ 𝓝 (0 : K) := hU.mem_nhds (h0U rfl)
  have hsub : Tendsto (fun xy : K × K => xy.1 - xy.2) (𝓝 a ×ˢ 𝓝 a) (𝓝 0) := by
    have h : Tendsto (fun xy : K × K => xy.1 - xy.2) (𝓝 (a, a)) (𝓝 (a - a)) :=
      (continuous_fst.sub continuous_snd : Continuous fun xy : K × K => xy.1 - xy.2).tendsto (a, a)
    rwa [nhds_prod_eq, sub_self] at h
  obtain ⟨N, hN, hNN⟩ := Filter.mem_prod_self_iff.1 (hsub hU0)
  have hfreq : ∃ᶠ n : ℕ in atTop, (n : K) * z ∈ N :=
    MapClusterPt.frequently (u := fun n : ℕ => (n : K) * z) ha hN
  obtain ⟨n, _, hn⟩ := hfreq.forall_exists_of_atTop 0
  obtain ⟨m, hm, hmN⟩ := hfreq.forall_exists_of_atTop (n + 1)
  have hk : ((m - n : ℕ) : K) * z ∈ U := by
    have h3 := hNN (Set.mk_mem_prod hmN hn)
    simp only [Set.mem_preimage] at h3
    rw [Nat.cast_sub (by omega), sub_mul]
    exact h3
  obtain ⟨u, hu⟩ := hQ (m - n) (by omega)
  obtain ⟨c, hc⟩ := vnr z
  have hy : (↑u⁻¹ * c) * z ∈ J := hJmul _ _ hzJ
  apply hUV (Set.mk_mem_prod hk (hJV hy))
  show ((m - n : ℕ) : K) * z * (↑u⁻¹ * c * z) = z
  rw [← hu]
  have h4 : (u : K) * ↑u⁻¹ = 1 := u.mul_inv
  linear_combination (z * z * c) * h4 - hc
end Formalism.FourierDecayAlt.P.A6x4
