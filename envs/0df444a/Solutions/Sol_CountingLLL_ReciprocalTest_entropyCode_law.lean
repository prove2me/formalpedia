-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.entropyCode_law
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:07:59.06519+00:00
-- url     : https://prove2.me/submissions/ffb4fd81-61d9-42a4-a18f-09caee8fd536

import Definitions.Def_CountingLLL_ReciprocalEncodedLaw
import Theorems.Thm_CountingLLL_ReciprocalTest_infinitePi_sum_merge
import Theorems.Thm_CountingLLL_ReciprocalTest_encoded_read_marginals
set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal

theorem solution (B : ℝ≥0∞) (hB : B ≤ 1) :
    (entropyLaw B).map entropyCode = encodedEntropyLaw B := by
  classical
  letI (i : ReadIndex) : IsProbabilityMeasure (readLaw B i) := (encoded_read_marginals B hB).1 i
  letI : IsProbabilityMeasure (oracleLaw B) := by
    constructor
    simp only [oracleLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [add_comm, tsub_add_cancel_of_le hB]
  letI : IsProbabilityMeasure fairLaw := by
    constructor
    simp only [fairLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← two_mul, one_div, ENNReal.mul_inv_cancel (by norm_num) (by simp)]
  letI (a : ℕ × ℕ) : IsProbabilityMeasure (uniformLaw a.1) := by
    constructor
    simp [uniformLaw, Measure.smul_apply, Measure.count_apply, ENNReal.inv_mul_cancel]
  let O : (ℕ → Bool) → (ℕ → ℕ) := fun x i => bitCode (x i)
  let F : (ℕ → Bool) → (ℕ → ℕ) := fun x i => bitCode (x i)
  let U : ((a : ℕ × ℕ) → Fin (a.1+1)) → ((ℕ × ℕ) → ℕ) := fun x a => (x a).val
  have hO : Measurable O := by fun_prop
  have hF : Measurable F := by fun_prop
  have hU : Measurable U := by fun_prop
  let μo := Measure.infinitePi fun _ : ℕ => oracleLaw B
  let μf := Measure.infinitePi fun _ : ℕ => fairLaw
  let μu := Measure.infinitePi fun a : ℕ × ℕ => uniformLaw a.1
  let κo : ℕ → Measure ℕ := fun i => readLaw B (.inl i)
  let κf : ℕ → Measure ℕ := fun i => readLaw B (.inr (.inl i))
  let κu : ℕ × ℕ → Measure ℕ := fun a => readLaw B (.inr (.inr a))
  have hmapO : μo.map O = Measure.infinitePi κo := by
    simpa [μo, O, κo, readLaw] using (Measure.infinitePi_map_pi (fun _ : ℕ => oracleLaw B) (f := fun _ => bitCode) (fun _ => by fun_prop))
  have hmapF : μf.map F = Measure.infinitePi κf := by
    simpa [μf, F, κf, readLaw] using (Measure.infinitePi_map_pi (fun _ : ℕ => fairLaw) (f := fun _ => bitCode) (fun _ => by fun_prop))
  have hmapU : μu.map U = Measure.infinitePi κu := by
    simpa [μu, U, κu, readLaw] using (Measure.infinitePi_map_pi (fun a : ℕ × ℕ => uniformLaw a.1) (f := fun a (x : Fin (a.1+1)) => x.val) (fun _ => by fun_prop))
  letI (x : ℕ ⊕ (ℕ × ℕ)) : IsProbabilityMeasure (Sum.elim κf κu x) := by
    cases x with
    | inl i => exact (encoded_read_marginals B hB).1 (.inr (.inl i))
    | inr a => exact (encoded_read_marginals B hB).1 (.inr (.inr a))
  let mergeR : ((ℕ → ℕ) × ((ℕ × ℕ) → ℕ)) → (ℕ ⊕ (ℕ × ℕ) → ℕ) := fun p => Sum.elim p.1 p.2
  let merge : ((ℕ → ℕ) × (ℕ ⊕ (ℕ × ℕ) → ℕ)) → (ReadIndex → ℕ) := fun p => Sum.elim p.1 p.2
  have hmergeR : Measurable mergeR := by
    apply measurable_pi_lambda; intro a; cases a with
    | inl i => exact (measurable_pi_apply i).comp measurable_fst
    | inr j => exact (measurable_pi_apply j).comp measurable_snd
  have hmerge : Measurable merge := by
    apply measurable_pi_lambda; intro a; cases a with
    | inl i => exact (measurable_pi_apply i).comp measurable_fst
    | inr j => exact (measurable_pi_apply j).comp measurable_snd
  have hblock : (μf.prod μu).map (fun x => mergeR (F x.1,U x.2)) = Measure.infinitePi (Sum.elim κf κu) := by
    have heq : (fun x => mergeR (F x.1,U x.2)) = mergeR ∘ Prod.map F U := rfl
    rw [heq, ← Measure.map_map hmergeR (hF.prodMap hU), ← Measure.map_prod_map μf μu hF hU, hmapF, hmapU]
    exact infinitePi_sum_merge κf κu
  have hwhole : (μo.prod (μf.prod μu)).map
      (fun x => merge (O x.1, mergeR (F x.2.1,U x.2.2))) =
      Measure.infinitePi (Sum.elim κo (Sum.elim κf κu)) := by
    let V := fun x : (ℕ → Bool) × ((a : ℕ × ℕ) → Fin (a.1+1)) => mergeR (F x.1,U x.2)
    have hV : Measurable V := hmergeR.comp (hF.comp measurable_fst |>.prodMk (hU.comp measurable_snd))
    have heq : (fun x => merge (O x.1, mergeR (F x.2.1,U x.2.2))) = merge ∘ Prod.map O V := rfl
    rw [heq, ← Measure.map_map hmerge (hO.prodMap hV), ← Measure.map_prod_map μo (μf.prod μu) hO hV, hmapO]
    change ((Measure.infinitePi κo).prod ((μf.prod μu).map (fun x => mergeR (F x.1,U x.2)))).map merge = _
    rw [hblock]
    exact infinitePi_sum_merge κo (Sum.elim κf κu)
  change (μo.prod (μf.prod μu)).map entropyCode = Measure.infinitePi (readLaw B)
  have heq : entropyCode = fun x => merge (O x.1, mergeR (F x.2.1,U x.2.2)) := by
    funext x i
    cases i with
    | inl i => rfl
    | inr a => cases a <;> rfl
  rw [heq, hwhole]
  congr 1
  funext i
  cases i with
  | inl i => rfl
  | inr a => cases a <;> rfl
