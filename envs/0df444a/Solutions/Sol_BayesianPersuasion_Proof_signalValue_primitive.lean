-- Prove2me | solution 1 for BayesianPersuasion.Proof.signalValue_primitive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:09:12.595877+00:00
-- url     : https://prove2.me/submissions/882030c7-9ee8-40ce-8ef6-b9df2f16e067

module
public import Definitions.Def_BayesianPersuasion_Signals
public import Definitions.Def_BayesianPersuasion_CompactHull
public import Mathlib.Analysis.Convex.Jensen
public import Definitions.Def_BayesianPersuasion_Attainment
public import Theorems.Thm_BayesianPersuasion_Proof_mass_mul_posterior
public import Theorems.Thm_BayesianPersuasion_Proof_senderPayoff_eq


set_option autoImplicit true
@[expose] public section
public section
universe uΩ uA
open Set Finset
open BayesianPersuasion
variable {Ω : Type uΩ} {A : Type uA} [Fintype Ω]
open BayesianPersuasion.Proof
namespace BayesianPersuasion.Proof
theorem _root_.solution [TopologicalSpace A] [CompactSpace A] [Nonempty A]
    (u v : A → Ω → ℝ) (hu : ∀ ω, Continuous (fun a => u a ω))
    (hv : ∀ ω, Continuous (fun a => v a ω)) (p : Belief Ω) {n : ℕ}
    (π : Signal Ω n) (a : Fin n → A)
    (ha : ∀ s, SenderPreferred u v (signalPosterior p π s) (a s)) :
    signalValue u v p π = ∑ ω, p.val ω * ∑ s, (π ω).val s * v (a s) ω := by
  have hf : ∀ s, senderPayoff u v (signalPosterior p π s) =
      expected v (signalPosterior p π s) (a s) := fun s => senderPayoff_eq u v hu hv _ (ha s)
  unfold signalValue
  simp_rw [hf, expected, Finset.mul_sum]
  calc
    (∑ s, ∑ ω, signalMass p π s * ((signalPosterior p π s).val ω * v (a s) ω)) =
        ∑ s, ∑ ω, p.val ω * ((π ω).val s * v (a s) ω) := by
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro ω _
      rw [← mul_assoc, mass_mul_posterior, mul_assoc]
    _ = _ := by rw [Finset.sum_comm]
end BayesianPersuasion.Proof
