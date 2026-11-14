-- Prove2me | solution 1 for CatalyticTreeEval.Main.theorem_1_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-13T23:07:14.26021+00:00
-- url     : https://prove2.me/submissions/37b264c0-32f8-4958-9dd1-e2ead933929c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_CatalyticTreeEval_Main_corollary_4_7

set_option autoImplicit false

namespace CatalyticTreeEval.Main

private lemma tableCode_length {l : ℕ} (f : Label l → Label l → Label l) :
    (tableCode f).length = 2 ^ l * (2 ^ l * l) := by
  simp [tableCode, bits, List.map_const', List.sum_replicate, Nat.mul_comm]

/-- Every leaf contributes its full label, so positive label length gives at least
one input bit for each of the `2^h` leaves. -/
private lemma leaves_le_payload {l h : ℕ} (hl : 0 < l) (I : Tree l h) :
    2 ^ h ≤ I.payload.length := by
  induction I with
  | leaf v => simpa [Tree.payload, bits] using (Nat.succ_le_of_lt hl)
  | @node h f a b ha hb =>
      simp only [Tree.payload, List.length_append, pow_succ]
      omega

/-- A positive-height tree includes the entire root table. -/
private lemma labels_le_payload {l h : ℕ} (hl : 0 < l) (hh : 0 < h)
    (I : Tree l h) : 2 ^ l ≤ I.payload.length := by
  cases I with
  | leaf v => omega
  | node f a b =>
      have hp : 1 ≤ 2 ^ l := Nat.one_le_pow l 2 (by omega)
      have hmul : 1 ≤ 2 ^ l * l := by nlinarith
      have htable : 2 ^ l ≤ (tableCode f).length := by
        rw [tableCode_length]
        nlinarith
      simp only [Tree.payload, List.length_append]
      omega

private lemma payload_le_encode {l h : ℕ} (I : Tree l h) :
    I.payload.length ≤ I.encode.length := by
  simp only [Tree.encode, List.length_append]
  omega

private lemma exponent_le_log₂ {k : ℕ} {n : ℝ} (hpow : (2 : ℝ) ^ k ≤ n) :
    (k : ℝ) ≤ log₂ n := by
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ k) hpow
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2 hlog

/-- Enlarging the allowed work, catalyst prefix, and time bounds preserves the
same halting run. The premise for longer tapes is transferred to the old bound. -/
private lemma computesPrefix_mono {M : Machine} {input output : List Bool}
    {s c t s' c' t' : ℝ} (H : ComputesPrefix M input output s c t)
    (hs : s ≤ s') (hc : c ≤ c') (ht : t ≤ t') :
    ComputesPrefix M input output s' c' t' := by
  intro τ hτ
  obtain ⟨steps, cfg, hrun, hhalt, hout, hrestore, hwork, htime, hprefix⟩ :=
    H τ ((Nat.ceil_le_ceil hc).trans hτ)
  refine ⟨steps, cfg, hrun, hhalt, hout, hrestore, ?_, htime.trans ht, ?_⟩
  · intro u hu cfg' hcfg'
    exact (hwork u hu cfg' hcfg').trans_le (Nat.ceil_le_ceil hs)
  · intro u hu cfg' hcfg'
    exact (hprefix u hu cfg' hcfg').trans_le (Nat.ceil_le_ceil hc)

end CatalyticTreeEval.Main

open CatalyticTreeEval.Main

/-- Theorem 1.1 follows from the parameterized evaluator of Corollary 4.7.
This is a reduction: Corollary 4.7 remains an open platform theorem. -/
theorem solution :
    ∀ ε : ℝ, 0 < ε →
    ∃ (M : Machine) (Cs Cc Ct : ℝ) (q : ℕ),
      0 < Cs ∧ 0 < Cc ∧ 0 < Ct ∧ 0 < q ∧
      ∀ (h l : ℕ), 0 < h → 0 < l → ∀ I : Tree l h,
      ComputesPrefix M I.encode (bits l I.value.val)
        (Cs * (1 + log₂ (I.encode.length + 2)))
        (exp₂ (Cc * (1 + log₂ (I.encode.length + 2)) ^ ε))
        (Ct * (I.encode.length + 2 : ℝ) ^ q) := by
  intro ε hε
  obtain ⟨M, Cs, Cc, Ct, q, hCs, hCc, hCt, hq, H⟩ := corollary_4_7 ε hε
  refine ⟨M, 2 * Cs, Cc, Ct, 2 * q, by positivity, hCc, hCt, by omega, ?_⟩
  intro h l hh hl I
  have hleaves : 2 ^ h ≤ I.encode.length :=
    (leaves_le_payload hl I).trans (payload_le_encode I)
  have hlabels : 2 ^ l ≤ I.encode.length :=
    (labels_le_payload hl hh I).trans (payload_le_encode I)
  have hheight : (2 : ℝ) ^ h ≤ (I.encode.length : ℝ) + 2 := by
    exact_mod_cast (show 2 ^ h ≤ I.encode.length + 2 by omega)
  have hlabel : (2 : ℝ) ^ l ≤ (I.encode.length : ℝ) + 2 := by
    exact_mod_cast (show 2 ^ l ≤ I.encode.length + 2 by omega)
  have hhlog := exponent_le_log₂ hheight
  have hllog := exponent_le_log₂ hlabel
  have hspace : Cs * (l + h : ℝ) ≤
      (2 * Cs) * (1 + log₂ (I.encode.length + 2)) := by
    nlinarith
  have hcat : exp₂ (Cc * (l : ℝ) ^ ε) ≤
      exp₂ (Cc * (1 + log₂ (I.encode.length + 2)) ^ ε) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    apply mul_le_mul_of_nonneg_left _ hCc.le
    exact Real.rpow_le_rpow (Nat.cast_nonneg l) (by linarith) hε.le
  have hsize : (2 : ℝ) ^ (l + h) ≤ ((I.encode.length : ℝ) + 2) ^ 2 := by
    rw [pow_add, pow_two]
    exact mul_le_mul hlabel hheight (by positivity) (by positivity)
  have htime : Ct * (2 : ℝ) ^ (q * (l + h)) ≤
      Ct * (I.encode.length + 2 : ℝ) ^ (2 * q) := by
    apply mul_le_mul_of_nonneg_left _ hCt.le
    calc
      (2 : ℝ) ^ (q * (l + h)) = ((2 : ℝ) ^ (l + h)) ^ q := by
        rw [← pow_mul, Nat.mul_comm q (l + h)]
      _ ≤ (((I.encode.length : ℝ) + 2) ^ 2) ^ q :=
        pow_le_pow_left₀ (by positivity) hsize q
      _ = (I.encode.length + 2 : ℝ) ^ (2 * q) := by rw [pow_mul]
  exact computesPrefix_mono (H h l hh hl I) hspace hcat htime
