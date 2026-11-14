-- Prove2me | solution 1 for CountingLLL.ContractedWalk.head_tail_independent
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:37:07.433458+00:00
-- url     : https://prove2.me/submissions/f043d771-ecfe-4dab-ae72-2f3c0ae39765

import Definitions.Def_CountingLLL_ContractedWalk

set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.ContractedWalk
open scoped ENNReal

private theorem bitLaw_probability' (p : ℝ≥0∞) (hp : p ≤ 1) : IsProbabilityMeasure (bitLaw p) := by
  constructor
  simp only [bitLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  exact tsub_add_cancel_of_le hp

theorem solution (p : ℝ≥0∞) (hp : p ≤ 1) :
    IndepFun (fun ω : Tape => ω 0) (fun ω : Tape => fun n => ω (n+1)) (tapeLaw p) := by
  classical
  letI : IsProbabilityMeasure (bitLaw p) := bitLaw_probability' p hp
  let μ := tapeLaw p
  letI : IsProbabilityMeasure μ := by dsimp [μ,tapeLaw]; infer_instance
  have hind : iIndepFun (fun k (ω : Tape) => ω k) μ := iIndepFun_infinitePi (fun _ => measurable_id)
  apply IndepFun.indepFun_process (measurable_pi_apply 0) (fun n => measurable_pi_apply (n+1))
  intro I
  let S : Finset ℕ := {0}
  let T : Finset ℕ := I.image (fun n => n+1)
  have hd : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro x hx hxt
    simp [S] at hx
    subst x
    simp [T] at hxt
  have h := iIndepFun.indepFun_finset S T hd hind (fun k => measurable_pi_apply k)
  let F : (S → Bool) → Bool := fun x => x ⟨0, by simp [S]⟩
  let G : (T → Bool) → (I → Bool) := fun x k => x ⟨k.val+1, Finset.mem_image.mpr ⟨k.val,k.property,rfl⟩⟩
  have hmF : Measurable F := measurable_pi_apply _
  have hmG : Measurable G := measurable_pi_lambda _ (fun k => measurable_pi_apply _)
  have hc := h.comp hmF hmG
  simpa [F,G,S,T,Function.comp_def] using hc
