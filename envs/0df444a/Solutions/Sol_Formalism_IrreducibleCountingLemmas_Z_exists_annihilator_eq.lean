-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.exists_annihilator_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:00:48.840828+00:00
-- url     : https://prove2.me/submissions/766ef4bf-03c8-4ed9-a42e-89fdc6b7bd92

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_SchurOrthogonalityCompact
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ExistsNeZeroAevalEqZero
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_exists_ne_zero_aeval_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open scoped TensorProduct
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z
namespace Formalism.IrreducibleCountingLemmas.Z
theorem _root_.solution {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g : Module.End K V) (hs : g.charpoly.Separable) (d : K[X]) :
    d ∣ g.charpoly → ∃ e : V, aeval g d e = 0 ∧ ∀ q : K[X], aeval g q e = 0 → d ∣ q := by
  classical
  have hm : ∀ (f h : Module.End K V) (x : V), (f * h) x = f (h x) := fun _ _ _ => rfl
  have hadd : ∀ (f h : Module.End K V) (x : V), (f + h) x = f x + h x := fun _ _ _ => rfl
  have hone : ∀ x : V, (1 : Module.End K V) x = x := fun _ => rfl
  have hkill : ∀ (s t : K[X]) (x : V), aeval g s x = 0 → aeval g (t * s) x = 0 := by
    intro s t x hx
    rw [map_mul, hm, hx, map_zero]
  have hsq : Squarefree g.charpoly := hs.squarefree
  refine WfDvdMonoid.induction_on_irreducible d ?_ ?_ ?_
  · intro h0
    exact absurd (zero_dvd_iff.1 h0) (LinearMap.charpoly_monic g).ne_zero
  · intro u hu _
    exact ⟨0, map_zero _, fun q _ => hu.dvd⟩
  · intro a i _ hi ih hdvd
    have ha : a ∣ g.charpoly := dvd_of_mul_left_dvd hdvd
    have hid : i ∣ g.charpoly := dvd_of_mul_right_dvd hdvd
    obtain ⟨ea, hea0, hea⟩ := ih ha
    obtain ⟨w, hw0, hw⟩ := exists_ne_zero_aeval_eq_zero g i hi hid
    have hcopOf : ∀ n : K[X], ¬ i ∣ n → IsCoprime i n := fun n h => by
      first
        | exact (Irreducible.coprime_iff_not_dvd hi).2 h
        | exact (Irreducible.isCoprime_iff_not_dvd hi).2 h
    have hcop : IsCoprime i a := hcopOf a fun hia =>
      hi.1 (hsq i (dvd_trans (mul_dvd_mul_left i hia) hdvd))
    refine ⟨ea + w, ?_, fun q hq => ?_⟩
    · rw [map_add, hkill a i ea hea0, mul_comm, hkill i a w hw, add_zero]
    · have hw' : aeval g (i * q) w = 0 := by
        rw [mul_comm]
        exact hkill i q w hw
      have hqi : aeval g (i * q) ea = 0 := by
        have h1 := hkill q i _ hq
        rwa [map_add, hw', add_zero] at h1
      have haq : a ∣ q := by
        have h2 : a ∣ i * q := hea _ hqi
        first
          | exact hcop.symm.dvd_of_dvd_mul_left h2
          | exact hcop.symm.dvd_of_dvd_mul_right (by rwa [mul_comm] at h2)
      have hea' : aeval g (a * q) ea = 0 := by
        rw [mul_comm]
        exact hkill a q ea hea0
      have hwq : aeval g (a * q) w = 0 := by
        have h1 := hkill q a _ hq
        rwa [map_add, hea', zero_add] at h1
      have hiaq : i ∣ a * q := by
        by_contra hn
        obtain ⟨u, t, hut⟩ := hcopOf _ hn
        apply hw0
        have h2 : aeval g (u * i + t * (a * q)) w = 0 := by
          rw [map_add, hadd, hkill i u w hw, hkill (a * q) t w hwq, add_zero]
        rwa [hut, map_one, hone] at h2
      have hiq : i ∣ q := by
        first
          | exact hcop.dvd_of_dvd_mul_left hiaq
          | exact hcop.dvd_of_dvd_mul_right (by rwa [mul_comm] at hiaq)
      exact hcop.mul_dvd hiq haq
end Formalism.IrreducibleCountingLemmas.Z
