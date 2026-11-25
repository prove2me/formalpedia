-- Prove2me | solution 2 for DetDLP.bounded_divisor_search_from_btn
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T05:21:06.335384+00:00
-- url     : https://prove2.me/submissions/920c4091-331f-4ec2-b177-9fb2831e9edf

import Definitions.Def_DetDLP_S6B_Budget
import Theorems.Thm_DetDLP_m89_polyT_oracle_loop
set_option autoImplicit false
open Groundwork DetDLP DetDLP.S6BWords DetDLP.S6BStep DetDLP.S6BPrefix DetDLP.S6BBudget
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

private noncomputable def rate (k d : ℕ) := (2:ℝ)^((k:ℝ)*d/Real.sqrt (logSafe d))
private theorem cost {L : ℕ → ℕ} (hL : PB L) (k a : ℕ) : ∃ C : ℕ, ∀ d : ℕ, 2 ≤ d →
    (4*d+1:ℕ)*(polyBound k (L d)+(k:ℝ)*(rate a d+polyBound a d+1)) ≤ rate C d ∧
    polyBound k (L d)+(k:ℝ)*(polyBound a d+1) ≤ polyBound C d := by
  let f := fun n => (4*n+1)*(P k (L n)+k*(P a n+2))
  have hf : PB f := (((PB.const 4).mul PB.id').add (PB.const 1)).mul ((Ppb k hL).add ((PB.const k).mul ((Ppb a PB.id').add (PB.const 2))))
  obtain ⟨j,hj⟩ := hf
  refine ⟨24*j+a,?_⟩
  intro d hd
  have h : ((4*d+1:ℕ):ℝ)*(polyBound k (L d)+(k:ℝ)*(polyBound a d+2)) ≤ polyBound j d := by
    have hr : (f d:ℝ) ≤ (P j d:ℝ) := by exact_mod_cast hj d
    simpa [f,Nat.cast_mul,Nat.cast_add,cast_P] using hr
  have e : 1 ≤ rate a d := Real.one_le_rpow (by norm_num) (by positivity)
  have p : 0 ≤ polyBound k (L d) := by unfold polyBound; positivity
  have s : 0 ≤ polyBound a d := by unfold polyBound; positivity
  have r : (1:ℝ) ≤ (4*d+1:ℕ) := by exact_mod_cast (show 1 ≤ 4*d+1 by omega)
  constructor
  · apply le_trans _ ((mul_le_mul_of_nonneg_right h (by linarith : 0 ≤ rate a d)).trans (w5_polyBound_mul_sqrtLogExp_le j a d hd))
    rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by positivity)
    have ht : rate a d+polyBound a d+1 ≤ (polyBound a d+2)*rate a d := by nlinarith [mul_nonneg s (sub_nonneg.mpr e)]
    nlinarith [mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg (α:=ℝ) k),mul_nonneg p (sub_nonneg.mpr e)]
  · apply le_trans _ (h.trans (w4_M5QueryBridge.polyBound_monoK (by omega)))
    apply le_trans _ (le_mul_of_one_le_left (by positivity) r)
    gcongr; norm_num

private def Runs (O : PrimitiveMachine) (o : Fin O.tapeCount) (t s : ℝ) :=
  Nat.rec (motive := fun _ => Wd → Wd → Wd → ℕ → Prop) (fun _ _ _ _ => False)
    (fun _ prev st ans out m =>
      (step (pair st ans) = true :: out ∧ (pair st ans).length ≤ m ∧ out.length ≤ m) ∨
      ∃ st' q ans', step (pair st ans) = false :: pair st' q ∧ (pair st ans).length ≤ m ∧
        (pair st' q).length ≤ m ∧ ans'.length ≤ m ∧ RunsWithin O o q ans' t s ∧ prev st' ans' out m)

private theorem rounds {O : PrimitiveMachine} {o : Fin O.tapeCount} {t s : ℝ} (w : Wd) {L : ℕ → ℕ} (hL : bounds L)
    (oracle : ∀ p, RunsWithin O o (req w p) (reply w p) t s) : ∀ n p st ans,
      n+p.length=4*w.length → step (pair st ans) = next w p → (pair st ans).length ≤ L w.length →
      Runs O o t s (n+1) st ans (readout w (grow (query w.length (Groundwork.PolyT.bval w)) n p)) (L w.length) := by
  intro n; induction n with
  | zero =>
    intro p st ans eq hs hl; have h := hL w p (by omega)
    exact Or.inl ⟨hs.trans (by simp [next,show ¬ p.length < 4*w.length by omega,grow]),hl,h.2.2.2.2⟩
  | succ n ih =>
    intro p st ans eq hs hl; have h := hL w p (by omega)
    refine Or.inr ⟨pair w p, req w p, reply w p,hs.trans (by simp [next,show p.length < 4*w.length by omega]),hl,h.2.1,h.2.2.2.1,oracle p,?_⟩
    apply ih (advance (query w.length (Groundwork.PolyT.bval w)) p)
    · simp [advance]; omega
    · exact step_reply w p
    · exact h.2.2.1

theorem solution
    (hcontract : ∀ (C A c0 : ℕ), 0 < C → 0 < A → 0 < c0 →
      ∀ (E : PrimitiveMachine) (outE : Fin E.tapeCount),
        ∃ (M : PrimitiveMachine) (outM : Fin M.tapeCount) (K : ℕ),
          ∀ (s P0 ℓ : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
            (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly P0 ℓ),
            2 ≤ s →
            G.nE ≤ C * s →
            G.nV ≤ s ^ c0 →
            G.maxDeg ≤ Nat.ceil ((s : ℝ) ^ ((9 : ℝ) / 10)) →
            1 ≤ P0 → P0 ≤ C * s →
            1 ≤ ℓ → ℓ ≤ C * s →
            BTNEntryEvaluable desc G P0 ℓ T E outE
              (((s + desc.length : ℕ) : ℝ) ^ c0 * (2 : ℝ) ^ ((A : ℝ) * (s : ℝ) ^ ((9 : ℝ) / 10)))
              (((s + desc.length : ℕ) : ℝ) ^ c0) →
            ∃ w : List Bool,
              EncodesTruncPoly P0 ℓ w (BTNContract G T) ∧
              RunsWithin M outM (encodeBTNInstance desc G s P0 ℓ) w
                (btnTimeBound K (s + desc.length) s)
                (polyBound K (s + desc.length)))
    (hmult : ∃ (E : PrimitiveMachine) (outE : Fin E.tapeCount) (K : ℕ),
      ∀ d : ℕ, 1 ≤ d →
        ∃ (G : BipartiteMultigraph)
          (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
          (ext : Fin (4 * d) → Fin G.nE),
          G.nE < 1100 * (d + 1) ∧
          (G.maxDeg : ℝ) < 136 * ((d : ℝ) + 1) ^ ((3 : ℝ) / 4) ∧
          (G.nV : ℝ) ≤ polyBound K d ∧
          BoolBTNEntryEvaluable (countWord d) G T E outE (polyBound K d) (polyBound K d) ∧
          IsParsimonious G T ext (fun x =>
            bitsToNat (fun i : Fin d => x ⟨i.val, by omega⟩) *
            bitsToNat (fun i : Fin d => x ⟨d + i.val, by omega⟩) =
            bitsToNat (fun i : Fin (2 * d) => x ⟨2 * d + i.val, by omega⟩))) :
    ∃ (f : ℕ → ℕ) (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
      ∀ N : ℕ, 2 ≤ N →
        (¬ N.Prime → 2 ≤ f N ∧ f N < N ∧ f N ∣ N) ∧
        let n := bitLen (N+1)
        RunsWithin M out (countWord N) (countWord (f N))
          ((2 : ℝ) ^ ((K : ℝ) * (n : ℝ) / Real.sqrt (logSafe (n : ℝ)))) (polyBound K n) := by
  obtain ⟨O,o,a,hO⟩ := S6BCountCall.uniform hcontract S6BPort.eval S6BPort.eval_poly S6BPort.eval_spec
  obtain ⟨M,out,k,_,loop⟩ := m89_polyT_oracle_loop step step_poly O o
  obtain ⟨L,hL,hB⟩ := sizeBudget
  obtain ⟨C,hC⟩ := cost hL k a
  refine ⟨fun N => answer (bitLen (N+1)) N,M,out,C,?_⟩
  intro N hN
  let w := countWord N
  have hd : w.length = bitLen (N+1) := w5_SplitArithmetic.countWord_length_eq_bitLen N (by omega)
  have hd2 : 2 ≤ w.length := hd.symm ▸ w5_M6CallBudget.two_le_bitLen_of_two_le hN
  have hn : N < 2^w.length := by rw [hd]; exact Nat.lt_of_lt_of_le (Nat.lt_succ_self N) (Nat.le_pow_clog (by decide) _)
  have hw : Groundwork.PolyT.bval w = N := w4_M5Evaluator.countWord_value N
  refine ⟨fun hc => answer_spec hN (hd ▸ hn) hc,?_⟩
  have hcall (p : Wd) : RunsWithin O o (req w p) (reply w p) (rate a w.length) (polyBound a w.length) := by
    rw [req,inst_eq _ _ (by omega),reply,hw]
    exact hO _ (by omega) _ hn _
  let n := w.length
  have hr := rounds w hB hcall (4*n) [] w [] (by simp [n]) (step_init w) ((hB w [] (by simp)).1)
  change Runs O o (rate a n) (polyBound a n) (4*n+1) w [] (readout w (grow (query w.length (Groundwork.PolyT.bval w)) (4*w.length) [])) (L n) at hr
  rw [readout_eq,hw] at hr
  have run := loop (rate a n) (polyBound a n) (by unfold rate; positivity) (by unfold polyBound; positivity) (4*n+1) (L n) w (countWord (answer n N)) (by omega) hr
  have res := PolyTBridge.runsWithin_mono_local run (hC n hd2).1 (hC n hd2).2
  simpa only [n,hd,rate] using res

#print axioms solution
