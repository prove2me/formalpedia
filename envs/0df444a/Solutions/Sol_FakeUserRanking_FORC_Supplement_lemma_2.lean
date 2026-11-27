-- Prove2me | solution 1 for FakeUserRanking.FORC.Supplement.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:25:30.432843+00:00
-- url     : https://prove2.me/submissions/4b6a5634-651e-4c50-abde-cca500ceb313

import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_Supplement_FAR
import Definitions.Def_FakeUserRanking_FORC_Supplement_EventE

open FakeUserRanking
open FakeUserRanking.FORC
open FakeUserRanking.FORC.Supplement

/-- Lemma 2 (Concentration Inequality), p. 21: under FAR with `δ = 1/(nT)`, against every fake-user
policy within the budget `F` that FAR is given, the event `E` of (8)–(9) has probability at least
`1 − δ²/(nT)`. -/
theorem solution (n T F : ℕ) (hn : 1 ≤ n) (hT : 1 ≤ T) (inst : Instance n)
    (P : Adversary n) (hP : WithinBudget F P)
    (tb : List (Fin 1 × Obs n) → Finset (Fin n) → Fin n)
    (fb : List (Fin 1 × Obs n) → Equiv.Perm (Fin n)) :
    1 - farDelta n T ^ 2 / ((n : ℝ) * T) ≤
      prob inst P (far n T F tb fb) T (eventE inst T F tb fb) := by
        classical
        open scoped BigOperators in
        set_option maxHeartbeats 3000000 in
          have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
          have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
          have hn0 : (0 : ℝ) < n := by linarith
          have hT0 : (0 : ℝ) < T := by linarith
          have harg : 2 * (n : ℝ) * T / farDelta n T = 2 * ((n : ℝ) * T) ^ 2 := by
            unfold farDelta
            field_simp
          have hlog : 0 < Real.log (2 * (n : ℝ) * T / farDelta n T) := by
            rw [harg]
            apply Real.log_pos
            nlinarith [mul_le_mul hnR hTR zero_le_one (by linarith : (0 : ℝ) ≤ n)]
          have havg_bounds (st : FarState n) (hs : ∀ i, st.clk i ≤ st.cnt i) (i : Fin n) :
              0 ≤ st.avg i ∧ st.avg i ≤ 1 := by
            unfold FarState.avg
            split_ifs with hz
            · exact ⟨le_rfl, zero_le_one⟩
            · constructor
              · positivity
              · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hz)).2
                exact_mod_cast hs i
          have hzero (st : FarState n) (i : Fin n) (hz : st.cnt i = 0) :
              st.avg i - farWindow n T F st i ≤ inst.μ i ∧
                inst.μ i ≤ st.avg i + farWindow n T F st i := by
            simp only [FarState.avg, farWindow, hz, ↓reduceIte]
            have hw : (1 : ℝ) ≤ max 1 (Real.sqrt (Real.log (2 * n * T / farDelta n T)) + F) := le_max_left _ _
            constructor <;> linarith [(inst.μ_mem i).1, (inst.μ_mem i).2]
          have hstate_bounds (h : List (Fin 1 × Obs n)) (i : Fin n) :
              (farState n T F tb fb h).clk i ≤ (farState n T F tb fb h).cnt i ∧
              (farState n T F tb fb h).cnt i ≤ h.length := by
            have hfold : ∀ (l : List (Fin 1 × Obs n)) (acc : List (Fin 1 × Obs n) × FarState n),
                (∀ j, acc.2.clk j ≤ acc.2.cnt j ∧ acc.2.cnt j ≤ acc.1.length) →
                ∀ j, (l.foldl (fun (a : List (Fin 1 × Obs n) × FarState n) x =>
                    (a.1 ++ [x], a.2.update n T F (farRank tb fb a.1 a.2) x.2)) acc).2.clk j ≤
                  (l.foldl (fun (a : List (Fin 1 × Obs n) × FarState n) x =>
                    (a.1 ++ [x], a.2.update n T F (farRank tb fb a.1 a.2) x.2)) acc).2.cnt j ∧
                (l.foldl (fun (a : List (Fin 1 × Obs n) × FarState n) x =>
                    (a.1 ++ [x], a.2.update n T F (farRank tb fb a.1 a.2) x.2)) acc).2.cnt j ≤
                  acc.1.length + l.length := by
              intro l
              induction l with
              | nil => intro acc ha j; simpa using ha j
              | cons x l ih =>
                intro acc ha j
                have hb : ∀ k, (acc.2.update n T F (farRank tb fb acc.1 acc.2) x.2).clk k ≤
                    (acc.2.update n T F (farRank tb fb acc.1 acc.2) x.2).cnt k ∧
                    (acc.2.update n T F (farRank tb fb acc.1 acc.2) x.2).cnt k ≤
                      (acc.1 ++ [x]).length := by
                  intro k
                  dsimp [FarState.update]
                  rcases ha k with ⟨hk1, hk2⟩
                  have hi : x.2.2 = true ∧ k = (farRank tb fb acc.1 acc.2) x.2.1 →
                      (farRank tb fb acc.1 acc.2).symm k ≤ x.2.1 := by
                    rintro ⟨_, rfl⟩
                    simp
                  by_cases hc : x.2.2 = true ∧ k = (farRank tb fb acc.1 acc.2) x.2.1
                  · have hf := hi hc
                    simp only [if_pos hc, if_pos hf, List.length_append, List.length_singleton]
                    constructor <;> omega
                  · simp only [if_neg hc, List.length_append, List.length_singleton]
                    split_ifs <;> constructor <;> omega
                have hc := ih (acc.1 ++ [x], acc.2.update n T F (farRank tb fb acc.1 acc.2) x.2) hb j
                simpa only [List.foldl_cons, List.length_cons, List.length_append, List.length_singleton,
                  Nat.add_assoc, Nat.add_comm 1, List.length_nil, Nat.zero_add] using hc
            simpa [farState, FarState.init] using hfold h ([], FarState.init) (by simp [FarState.init]) i
          have hreal_nonneg (π : Equiv.Perm (Fin n)) (o : Obs n) : 0 ≤ realW inst π o := by
            have hr (j : Fin n) : 0 ≤ reach inst π j := by
              unfold reach
              apply mul_nonneg <;> apply Finset.prod_nonneg <;> intro r hr
              · linarith [(inst.q_mem r).2]
              · linarith [(inst.μ_mem (π r)).2]
            rcases o with ⟨j, b⟩
            cases b <;> simp only [realW]
            · apply mul_nonneg
              · exact mul_nonneg (hr j) (sub_nonneg.mpr (inst.μ_mem _).2)
              · split_ifs
                · exact (inst.q_mem _).1
                · norm_num
            · exact mul_nonneg (hr j) (inst.μ_mem _).1
          have hobs_nonneg (π : Equiv.Perm (Fin n)) (a : Action n) (o : Obs n) :
              0 ≤ obsW inst π a o := by
            cases a <;> simp only [obsW]
            · exact hreal_nonneg π o
            · split_ifs <;> norm_num
          have htraj_nonneg (τ : Fin T → Step n 1) : 0 ≤ trajW inst P (far n T F tb fb) T τ := by
            unfold trajW
            apply Finset.prod_nonneg
            intro s hs
            dsimp [stepW, far]
            exact mul_nonneg (mul_nonneg zero_le_one ENNReal.toReal_nonneg) (hobs_nonneg _ _ _)
          have hprob_nonneg : 0 ≤ prob inst P (far n T F tb fb) T (eventE inst T F tb fb) := by
            unfold prob expect
            apply Finset.sum_nonneg
            intro τ hτ
            dsimp only
            split_ifs <;> simp [htraj_nonneg]
          have htree : ∀ (α : Type) [Fintype α] (K : List α → α → ℝ),
              (∀ h, ∑ x, K h x = 1) → ∀ m h,
              (∑ τ : Fin m → α, ∏ s : Fin m, K (h ++ (List.ofFn τ).take s) (τ s)) = 1 := by
            intro α _ K hK m
            induction m with
            | zero => intro h; simp
            | succ m ih =>
              intro h
              rw [← (Fin.snocEquiv (fun _ : Fin (m + 1) => α)).sum_comp]
              rw [Fintype.sum_prod_type, Finset.sum_comm]
              have ht (τ : Fin m → α) (x : α) (k : ℕ) (hk : k ≤ m) :
                  (List.ofFn (Fin.snoc τ x)).take k = (List.ofFn τ).take k := by
                rw [List.ofFn_succ']
                simp only [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append, List.take_append,
                  List.length_ofFn, Nat.sub_eq_zero_of_le hk, List.take_zero, List.append_nil]
              simp only [Fin.snocEquiv_apply, Fin.prod_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc]
              have hp (τ : Fin m → α) (x : α) :
                  (∏ s : Fin m, K (h ++ (List.ofFn (Fin.snoc τ x)).take s) (τ s)) =
                  ∏ s : Fin m, K (h ++ (List.ofFn τ).take s) (τ s) := by
                apply Finset.prod_congr rfl
                intro s hs
                rw [ht τ x s (by omega)]
              change (∑ τ : Fin m → α, ∑ x : α,
                (∏ s : Fin m, K (h ++ (List.ofFn (Fin.snoc τ x)).take s) (τ s)) *
                K (h ++ (List.ofFn (Fin.snoc τ x)).take m) x) = 1
              simp_rw [hp, ht _ _ m (le_refl _)]
              have hl (τ : Fin m → α) : (List.ofFn τ).take m = List.ofFn τ :=
                List.take_of_length_le (by simp)
              simp only [hl]
              simp_rw [← Finset.mul_sum, hK, mul_one]
              exact ih h
          have hbernoulli (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (u : ℝ) :
              p * Real.exp (u * (1 - p)) + (1 - p) * Real.exp (u * (-p)) ≤ Real.exp (u ^ 2 / 8) := by
            let ν := ProbabilityTheory.bernoulliMeasure true false (⟨p, hp⟩ : unitInterval)
            let X : Bool → ℝ := fun b => if b then 1 - p else -p
            have hm : Measurable X := measurable_from_top
            have hb : ∀ᵐ b ∂ν, X b ∈ Set.Icc (-p) (1 - p) := by
              apply Filter.Eventually.of_forall
              intro b
              cases b <;> simp [X] <;> linarith
            have hz : ∫ b, X b ∂ν = 0 := by
              dsimp [ν]
              rw [ProbabilityTheory.integral_bernoulliMeasure]
              simp [X]
              ring
            have hh := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hm.aemeasurable hb hz
            have hmg := hh.mgf_le u
            have hd : 1 - p - -p = (1 : ℝ) := by ring
            norm_num [ProbabilityTheory.mgf, ν, ProbabilityTheory.integral_bernoulliMeasure, X, hd,
              NNReal.coe_pow, NNReal.coe_div, Real.norm_eq_abs] at hmg
            convert hmg using 1 <;> congr 1 <;> ring
          have hreal_sum (π : Equiv.Perm (Fin n)) : ∑ o : Obs n, realW inst π o = 1 := by
            let q' : Fin n → ℝ := fun r => if (r : ℕ) + 1 < n then inst.q r else 1
            let a : Fin n → ℝ := fun r => (1 - inst.μ (π r)) * (1 - q' r)
            have hre (j : Fin n) : reach inst π j = ∏ r ∈ Finset.Iio j, a r := by
              rw [reach, ← Finset.prod_mul_distrib]
              apply Finset.prod_congr rfl
              intro r hr
              have hlt : (r : ℕ) + 1 < n := by
                have hrj : r < j := Finset.mem_Iio.mp hr
                have hj := j.isLt
                omega
              simp [a, q', hlt, mul_comm]
            have hpair (j : Fin n) : realW inst π (j, false) + realW inst π (j, true) =
                (1 - a j) * ∏ r ∈ Finset.Iio j, a r := by
              simp only [realW]
              change reach inst π j * (1 - inst.μ (π j)) * q' j +
                reach inst π j * inst.μ (π j) = _
              rw [hre]
              dsimp [a]
              ring
            have hz : ∏ r : Fin n, a r = 0 := by
              let j : Fin n := ⟨n - 1, by omega⟩
              apply Finset.prod_eq_zero (Finset.mem_univ j)
              have hj : ¬(j : ℕ) + 1 < n := by dsimp [j]; omega
              simp [a, q', hj]
            have ht := Finset.prod_one_sub_ordered Finset.univ (fun r : Fin n => 1 - a r)
            have hf (j : Fin n) : Finset.univ.filter (fun r : Fin n => r < j) = Finset.Iio j := by
              ext r
              simp
            simp only [sub_sub_cancel, hf] at ht
            rw [hz] at ht
            rw [Fintype.sum_prod_type]
            simp only [Fintype.sum_bool, add_comm (realW inst π (_, true)), hpair]
            linarith
          have hobs_sum (π : Equiv.Perm (Fin n)) (a : Action n) : ∑ o : Obs n, obsW inst π a o = 1 := by
            cases a with
            | none => exact hreal_sum π
            | some a => simp [obsW]
          have hpmf_sum (p : PMF (Action n)) : ∑ a, (p a).toReal = 1 := by
            have hh : ∑ a, p a = 1 := by simpa only [tsum_fintype] using p.tsum_coe
            rw [← ENNReal.toReal_sum (fun a _ => p.apply_ne_top a), hh]
            simp
          let A := far n T F tb fb
          let ah : List (Step n 1) → List (Fin 1 × Obs n) := fun h => h.map (fun s => (s.1, s.2.2))
          let rh : List (Step n 1) → Equiv.Perm (Fin n) := fun h => A.rank (ah h) 0
          let ph : List (Step n 1) → List (PubStep n) := fun h =>
            h.mapIdx (fun j s => (rh (h.take j), s.2.1.isSome, s.2.2))
          let K : List (Step n 1) → Step n 1 → ℝ := fun h s =>
            (P (ph h) s.2.1).toReal * obsW inst (rh h) s.2.1 s.2.2
          have hK_nonneg (h : List (Step n 1)) (s : Step n 1) : 0 ≤ K h s := by
            exact mul_nonneg ENNReal.toReal_nonneg (hobs_nonneg _ _ _)
          have hK_sum (h : List (Step n 1)) : ∑ s, K h s = 1 := by
            simp only [K, Fintype.sum_prod_type, Finset.sum_mul, ← Finset.mul_sum, hobs_sum, mul_one]
            simpa using hpmf_sum (P (ph h))
          have hph (τ : Fin T → Step n 1) (t : ℕ) : ph ((List.ofFn τ).take t) = pubHist A τ t := by
            apply List.ext_getElem
            · simp [ph, pubHist]
            · intro j hj hj'
              have hjT : j < T := by simpa [ph] using lt_of_lt_of_le hj (by simp [ph])
              have hjt : j < t := by
                have : j < min t T := by simpa [ph] using hj
                omega
              have htake : min j t = j := Nat.min_eq_left (by omega)
              simp [ph, pubHist, ranking, rh, ah, algHist, List.take_take, htake,
                Subsingleton.elim (τ ⟨j, hjT⟩).1 (0 : Fin 1)]
          have hKW (τ : Fin T → Step n 1) (s : Fin T) :
              K ((List.ofFn τ).take s) (τ s) = stepW inst P A τ s := by
            have hl : (τ s).1 = (0 : Fin 1) := Subsingleton.elim _ _
            simp only [K, hph, stepW, A, far, one_mul]
            congr 1
          have hmass : ∑ τ : Fin T → Step n 1, trajW inst P A T τ = 1 := by
            have hh := htree (Step n 1) K hK_sum T []
            simpa only [List.nil_append, hKW, trajW] using hh
          have hreal_before (π : Equiv.Perm (Fin n)) (j : Fin n) :
              (∑ o : Obs n, if o.1 < j then realW inst π o else 0) = 1 - reach inst π j := by
            let q' : Fin n → ℝ := fun r => if (r : ℕ) + 1 < n then inst.q r else 1
            let a : Fin n → ℝ := fun r => (1 - inst.μ (π r)) * (1 - q' r)
            have hre (k : Fin n) : reach inst π k = ∏ r ∈ Finset.Iio k, a r := by
              rw [reach, ← Finset.prod_mul_distrib]
              apply Finset.prod_congr rfl
              intro r hr
              have hlt : (r : ℕ) + 1 < n := by
                have hrk : r < k := Finset.mem_Iio.mp hr
                have hk := k.isLt
                omega
              simp [a, q', hlt, mul_comm]
            have hpair (k : Fin n) : realW inst π (k, true) + realW inst π (k, false) =
                (1 - a k) * ∏ r ∈ Finset.Iio k, a r := by
              simp only [realW]
              change reach inst π k * inst.μ (π k) +
                reach inst π k * (1 - inst.μ (π k)) * q' k = _
              rw [hre]
              dsimp [a]
              ring
            have ht := Finset.prod_one_sub_ordered (Finset.Iio j) (fun r : Fin n => 1 - a r)
            have hf (k : Fin n) (hk : k ∈ Finset.Iio j) :
                (Finset.Iio j).filter (fun r : Fin n => r < k) = Finset.Iio k := by
              ext r
              have hkj : k < j := Finset.mem_Iio.mp hk
              simp only [Finset.mem_filter, Finset.mem_Iio]
              exact ⟨fun h => h.2, fun h => ⟨lt_trans h hkj, h⟩⟩
            simp only [sub_sub_cancel] at ht
            have hh : (∑ k ∈ Finset.Iio j, (1 - a k) *
                ∏ r ∈ (Finset.Iio j).filter (fun r => r < k), a r) =
                ∑ k ∈ Finset.Iio j, (1 - a k) * ∏ r ∈ Finset.Iio k, a r := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [hf k hk]
            rw [hh] at ht
            rw [Fintype.sum_prod_type]
            simp only [Fintype.sum_bool]
            have hs : (∑ k : Fin n, ((if k < j then realW inst π (k, true) else 0) +
                (if k < j then realW inst π (k, false) else 0))) =
                ∑ k ∈ Finset.Iio j, (1 - a k) * ∏ r ∈ Finset.Iio k, a r := by
              have hite (k : Fin n) :
                  ((if k < j then realW inst π (k, true) else 0) +
                    (if k < j then realW inst π (k, false) else 0)) =
                  if k < j then realW inst π (k, true) + realW inst π (k, false) else 0 := by
                split_ifs <;> simp
              simp_rw [hite]
              rw [← Finset.sum_filter]
              have hhf : Finset.univ.filter (fun k : Fin n => k < j) = Finset.Iio j := by ext k; simp
              rw [hhf]
              apply Finset.sum_congr rfl
              intro k hk
              simp only [if_pos (Finset.mem_Iio.mp hk), hpair]
            rw [hs, hre]
            linarith
          let seen : Equiv.Perm (Fin n) → Fin n → Obs n → ℝ := fun π i o =>
            if π.symm i ≤ o.1 then 1 else 0
          let clicked : Equiv.Perm (Fin n) → Fin n → Obs n → ℝ := fun π i o =>
            if o.2 = true ∧ i = π o.1 then 1 else 0
          have hclick_seen (π : Equiv.Perm (Fin n)) (i : Fin n) (o : Obs n) :
              clicked π i o ≤ seen π i o := by
            dsimp [clicked, seen]
            have hi : o.2 = true ∧ i = π o.1 → π.symm i ≤ o.1 := by
              rintro ⟨_, rfl⟩
              simp
            by_cases hc : o.2 = true ∧ i = π o.1
            · simp only [if_pos hc, if_pos (hi hc), le_refl]
            · simp only [if_neg hc]; split_ifs <;> norm_num
          have hseen_mass (π : Equiv.Perm (Fin n)) (i : Fin n) :
              (∑ o : Obs n, realW inst π o * seen π i o) = reach inst π (π.symm i) := by
            have hh : (∑ o : Obs n, realW inst π o * seen π i o) +
                (∑ o : Obs n, if o.1 < π.symm i then realW inst π o else 0) = 1 := by
              rw [← Finset.sum_add_distrib, ← hreal_sum π]
              apply Finset.sum_congr rfl
              intro o ho
              dsimp [seen]
              by_cases hs : π.symm i ≤ o.1
              · simp only [if_pos hs, if_neg (not_lt.mpr hs), mul_one, add_zero]
              · simp only [if_neg hs, if_pos (lt_of_not_ge hs), mul_zero, zero_add]
            rw [hreal_before] at hh
            linarith
          have hclicked_mass (π : Equiv.Perm (Fin n)) (i : Fin n) :
              (∑ o : Obs n, realW inst π o * clicked π i o) = reach inst π (π.symm i) * inst.μ i := by
            rw [Fintype.sum_prod_type]
            simp only [Fintype.sum_bool, clicked, Bool.false_eq_true, false_and, ↓reduceIte,
              mul_zero, add_zero, true_and]
            have hi (k : Fin n) : i = π k ↔ k = π.symm i := by
              constructor
              · intro h; rw [h]; simp
              · rintro rfl; simp
            simp only [hi]
            simp [realW]
          have hreal_mgf (π : Equiv.Perm (Fin n)) (i : Fin n) (u : ℝ) :
              (∑ o : Obs n, realW inst π o *
                Real.exp (u * (clicked π i o - inst.μ i * seen π i o) - u ^ 2 / 8 * seen π i o)) ≤ 1 := by
            let v₀ := Real.exp (u * (-inst.μ i) - u ^ 2 / 8)
            let v₁ := Real.exp (u * (1 - inst.μ i) - u ^ 2 / 8)
            have hid (o : Obs n) :
                Real.exp (u * (clicked π i o - inst.μ i * seen π i o) - u ^ 2 / 8 * seen π i o) =
                  1 + (v₀ - 1) * seen π i o + (v₁ - v₀) * clicked π i o := by
              by_cases hc : o.2 = true ∧ i = π o.1
              · have hf : π.symm i ≤ o.1 := by rcases hc with ⟨_, rfl⟩; simp
                simp only [clicked, seen, if_pos hc, if_pos hf, mul_one, v₁]
                ring
              · by_cases hf : π.symm i ≤ o.1
                · simp only [clicked, seen, if_neg hc, if_pos hf, mul_one, mul_zero, sub_zero, zero_sub, v₀]
                  ring
                · simp [clicked, seen, hc, hf]
            simp_rw [hid]
            simp only [mul_add, Finset.sum_add_distrib]
            simp_rw [show ∀ o, realW inst π o * ((v₀ - 1) * seen π i o) =
              (v₀ - 1) * (realW inst π o * seen π i o) by intro o; ring]
            simp_rw [show ∀ o, realW inst π o * ((v₁ - v₀) * clicked π i o) =
              (v₁ - v₀) * (realW inst π o * clicked π i o) by intro o; ring]
            simp only [mul_one, ← Finset.mul_sum, hreal_sum, hseen_mass, hclicked_mass]
            have hb := hbernoulli (inst.μ i) (inst.μ_mem i) u
            have hv : inst.μ i * v₁ + (1 - inst.μ i) * v₀ ≤ 1 := by
              have he := Real.exp_pos (-(u ^ 2 / 8))
              have hh := mul_le_mul_of_nonneg_right hb he.le
              rw [← Real.exp_add] at hh
              have hz : u ^ 2 / 8 + -(u ^ 2 / 8) = 0 := by ring
              rw [hz, Real.exp_zero] at hh
              simpa only [add_mul, mul_assoc, ← Real.exp_add, sub_eq_add_neg, v₀, v₁] using hh
            have hr : 0 ≤ reach inst π (π.symm i) := by
              unfold reach
              apply mul_nonneg <;> apply Finset.prod_nonneg <;> intro r hr
              · linarith [(inst.q_mem r).2]
              · linarith [(inst.μ_mem (π r)).2]
            nlinarith [mul_nonneg hr (sub_nonneg.mpr hv)]
          have hmap_append (β : Type) (f : List (Step n 1) → Step n 1 → β)
              (h : List (Step n 1)) (x : Step n 1) :
              (h ++ [x]).mapIdx (fun j s => f ((h ++ [x]).take j) s) =
                h.mapIdx (fun j s => f (h.take j) s) ++ [f h x] := by
            rw [List.mapIdx_append]
            have hm : h.mapIdx (fun j s => f ((h ++ [x]).take j) s) =
                h.mapIdx (fun j s => f (h.take j) s) := by
              apply List.ext_getElem (by simp)
              intro j hj hj'
              have hjh : j < h.length := by simpa using hj
              simp only [List.getElem_mapIdx]
              rw [List.take_append_of_le_length (Nat.le_of_lt hjh)]
            rw [hm]
            simp
          have hph_append (h : List (Step n 1)) (x : Step n 1) :
              ph (h ++ [x]) = ph h ++ [(rh h, x.2.1.isSome, x.2.2)] := by
            exact hmap_append _ (fun h s => (rh h, s.2.1.isSome, s.2.2)) h x
          let datum : List (Step n 1) → Fin n → Step n 1 → List (Bool × Bool) := fun h i s =>
            if (rh h).symm i ≤ s.2.2.1 then
              [(s.2.1.isNone, s.2.2.2 && decide (i = rh h s.2.2.1))] else []
          let data : List (Step n 1) → Fin n → List (Bool × Bool) := fun h i =>
            (h.mapIdx (fun j s => datum (h.take j) i s)).flatten
          have hdata_nil (i : Fin n) : data [] i = [] := rfl
          have hdata_append (h : List (Step n 1)) (x : Step n 1) (i : Fin n) :
              data (h ++ [x]) i = data h i ++ datum h i x := by
            dsimp only [data]
            rw [hmap_append _ (fun h s => datum h i s) h x, List.flatten_append]
            simp
          let B : List (Step n 1) → ℕ := fun h => ((ph h).filter (fun s => s.2.1)).length
          have hB_nil : B [] = 0 := rfl
          have hB_append (h : List (Step n 1)) (x : Step n 1) :
              B (h ++ [x]) = B h + if x.2.1.isSome then 1 else 0 := by
            cases hx : x.2.1.isSome <;> simp [B, hph_append, hx]
          let st : List (Step n 1) → FarState n := fun h => farState n T F tb fb (ah h)
          have hst_append (h : List (Step n 1)) (x : Step n 1) :
              st (h ++ [x]) = (st h).update n T F (rh h) x.2.2 := by
            let f : List (Fin 1 × Obs n) × FarState n → Fin 1 × Obs n →
                List (Fin 1 × Obs n) × FarState n := fun acc x =>
              (acc.1 ++ [x], acc.2.update n T F (farRank tb fb acc.1 acc.2) x.2)
            have hh : ∀ (l : List (Fin 1 × Obs n)) (acc : List (Fin 1 × Obs n) × FarState n),
                (l.foldl f acc).1 = acc.1 ++ l := by
              intro l
              induction l with
              | nil => intro acc; simp
              | cons y l ih => intro acc; simp [List.foldl_cons, ih, f, List.append_assoc]
            have hhist : ((ah h).foldl f ([], FarState.init)).1 = ah h := by simpa using hh (ah h) ([], FarState.init)
            change ((ah (h ++ [x])).foldl f ([], FarState.init)).2 = _
            simp only [ah, List.map_append, List.map_cons, List.map_nil, List.foldl_append, List.foldl_cons,
              List.foldl_nil]
            dsimp only [f]
            change ((st h).update n T F
              (farRank tb fb (((ah h).foldl f ([], FarState.init)).1) (st h)) x.2.2) = _
            rw [hhist]
            rfl
          have hstats (h : List (Step n 1)) (i : Fin n) :
              (st h).cnt i = (data h i).length ∧
              (st h).clk i = ((data h i).map (fun z => if z.2 then 1 else 0)).sum := by
            induction h using List.reverseRecOn with
            | nil => simp [st, ah, farState, FarState.init, data]
            | append_singleton h x ih =>
              rw [hst_append, hdata_append]
              dsimp [FarState.update, datum]
              rcases ih with ⟨hc, hk⟩
              by_cases hs : (rh h).symm i ≤ x.2.2.1
              · simp only [if_pos hs, List.length_append, List.length_singleton, List.map_append,
                  List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
                constructor
                · omega
                · have hb : (x.2.2.2 && decide (i = rh h x.2.2.1)) = true ↔
                      x.2.2.2 = true ∧ i = rh h x.2.2.1 := by simp
                  simp only [Bool.and_eq_true, decide_eq_true_eq]
                  split_ifs <;> omega
              · have hnclick : ¬(x.2.2.2 = true ∧ i = rh h x.2.2.1) := by
                  rintro ⟨_, hi⟩
                  apply hs
                  rw [hi]
                  simp
                simp [hs, hnclick, hc, hk]
          let W : List (Step n 1) → {m : ℕ} → (Fin m → Step n 1) → ℝ :=
            fun h {m} τ => ∏ s : Fin m, K (h ++ (List.ofFn τ).take (s : ℕ)) (τ s)
          have hW_nonneg (h : List (Step n 1)) {m : ℕ} (τ : Fin m → Step n 1) : 0 ≤ W h τ := by
            exact Finset.prod_nonneg (fun _ _ => hK_nonneg _ _)
          have hW_cons (h : List (Step n 1)) {m : ℕ} (x : Step n 1) (τ : Fin m → Step n 1) :
              W h (Fin.cons x τ) = K h x * W (h ++ [x]) τ := by
            simp [W, Fin.prod_univ_succ, List.ofFn_succ, List.append_assoc]
          have hWmodel (τ : Fin T → Step n 1) : W [] τ = trajW inst P A T τ := by
            simp only [W, List.nil_append, hKW, trajW]
          have htree_le (V : List (Step n 1) → ℝ)
              (hs : ∀ h, ∑ x, K h x * V (h ++ [x]) ≤ V h) :
              ∀ m h, (∑ τ : Fin m → Step n 1, W h τ * V (h ++ List.ofFn τ)) ≤ V h := by
            intro m
            induction m with
            | zero => intro h; simp [W]
            | succ m ih =>
              intro h
              rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => Step n 1)).sum_comp,
                Fintype.sum_prod_type]
              change (∑ x, ∑ τ : Fin m → Step n 1, W h (Fin.cons x τ) * V (h ++ List.ofFn (Fin.cons x τ))) ≤ _
              simp_rw [hW_cons, List.ofFn_succ]
              simp only [mul_assoc, ← Finset.mul_sum]
              have hix (x : Step n 1) :
                  (∑ τ : Fin m → Step n 1, W (h ++ [x]) τ * V (h ++ x :: List.ofFn τ)) ≤ V (h ++ [x]) := by
                simpa only [List.append_assoc, List.singleton_append] using ih (h ++ [x])
              exact (Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hix x)
                (hK_nonneg h x))).trans (hs h)
          have hB_step (h : List (Step n 1)) (x : Step n 1) (hb : B h ≤ F) (hx : K h x ≠ 0) :
              B (h ++ [x]) ≤ F := by
            rw [hB_append]
            by_cases hh : F ≤ B h
            · have hp := hP (ph h) hh
              have hn : x.2.1 = none := by
                by_contra ha
                have hz : (P (ph h) x.2.1).toReal = 0 := by simp [hp, PMF.pure_apply, ha]
                exact hx (by simp [K, hz])
              simp [hn, hb]
            · have hlt : B h < F := by omega
              split_ifs <;> omega
          have hbudget : ∀ m h, B h ≤ F → ∀ τ : Fin m → Step n 1,
              W h τ ≠ 0 → B (h ++ List.ofFn τ) ≤ F := by
            intro m
            induction m with
            | zero => intro h hb τ hz; simpa using hb
            | succ m ih =>
              intro h hb τ
              refine Fin.consCases (fun x τ hz => ?_) τ
              rw [hW_cons] at hz
              have hx := (mul_ne_zero_iff.mp hz).1
              have ht := (mul_ne_zero_iff.mp hz).2
              simpa [List.ofFn_succ, List.append_assoc] using ih (h ++ [x]) (hB_step h x hb hx) τ ht
          have hfake_data (h : List (Step n 1)) (i : Fin n) :
              ((data h i).filter (fun z => !z.1)).length ≤ B h := by
            induction h using List.reverseRecOn with
            | nil => simp [hdata_nil, hB_nil]
            | append_singleton h x ih =>
              rw [hdata_append, hB_append]
              dsimp [datum]
              cases ha : x.2.1 <;>
                simp only [ha, Option.isNone_none, Option.isNone_some, Option.isSome_none, Option.isSome_some,
                  Bool.false_eq_true, ↓reduceIte] <;>
                split_ifs <;> simp [List.filter_append] <;> omega
          have hstep_mgf (h : List (Step n 1)) (i : Fin n) (u : ℝ) :
              (∑ s : Step n 1, K h s * Real.exp
                (u * (if s.2.1 = none then clicked (rh h) i s.2.2 - inst.μ i * seen (rh h) i s.2.2 else 0) -
                  u ^ 2 / 8 * seen (rh h) i s.2.2)) ≤ 1 := by
            have ha (a : Action n) :
                (∑ o : Obs n, obsW inst (rh h) a o * Real.exp
                  (u * (if a = none then clicked (rh h) i o - inst.μ i * seen (rh h) i o else 0) -
                    u ^ 2 / 8 * seen (rh h) i o)) ≤ 1 := by
              cases a with
              | none => simpa only [if_pos rfl, obsW, ↓reduceIte] using hreal_mgf (rh h) i u
              | some a =>
                calc
                  _ ≤ ∑ o : Obs n, obsW inst (rh h) (some a) o := by
                    apply Finset.sum_le_sum
                    intro o ho
                    have he : Real.exp (u * (if (some a : Action n) = none then
                        clicked (rh h) i o - inst.μ i * seen (rh h) i o else 0) - u ^ 2 / 8 * seen (rh h) i o) ≤ 1 := by
                      apply Real.exp_le_one_iff.mpr
                      simp only [Option.some_ne_none, ↓reduceIte, mul_zero, zero_sub]
                      have hsn : 0 ≤ seen (rh h) i o := by dsimp [seen]; split_ifs <;> norm_num
                      exact neg_nonpos.mpr (mul_nonneg (by positivity) hsn)
                    exact mul_le_of_le_one_right (hobs_nonneg _ _ _) he
                  _ = 1 := hobs_sum _ _
            simp only [Fintype.sum_prod_type, K]
            simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
            simp_rw [mul_assoc, ← Finset.mul_sum]
            calc
              _ ≤ ∑ a : Action n, (P (ph h) a).toReal * 1 := by
                exact Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (by simpa only [Fintype.sum_prod_type] using ha a) ENNReal.toReal_nonneg)
              _ = 1 := by simpa using hpmf_sum (P (ph h))
          let dev : Fin n → Bool × Bool → ℝ := fun i z =>
            if z.1 then (if z.2 then 1 else 0) - inst.μ i else 0
          let D : Fin n → ℕ → List (Step n 1) → ℝ := fun i k h =>
            (((data h i).take k).map (dev i)).sum
          let C : Fin n → ℕ → List (Step n 1) → ℕ := fun i k h => min k (data h i).length
          have htake_sum (l : List (Bool × Bool)) (z : Bool × Bool) (f : Bool × Bool → ℝ) (k : ℕ) :
              (((l ++ [z]).take k).map f).sum = ((l.take k).map f).sum + if l.length < k then f z else 0 := by
            by_cases hk : l.length < k
            · rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by omega)]
              simp [hk]
            · rw [List.take_append_of_le_length (by omega)]
              simp [hk]
          have hDC_step (i : Fin n) (k : ℕ) (h : List (Step n 1)) (s : Step n 1) :
              D i k (h ++ [s]) = D i k h +
                (if (data h i).length < k then
                  (if s.2.1 = none then clicked (rh h) i s.2.2 - inst.μ i * seen (rh h) i s.2.2 else 0) else 0) ∧
              (C i k (h ++ [s]) : ℝ) = C i k h +
                (if (data h i).length < k then seen (rh h) i s.2.2 else 0) := by
            dsimp only [D, C]
            rw [hdata_append]
            by_cases hs : (rh h).symm i ≤ s.2.2.1
            · simp only [datum, if_pos hs, htake_sum, List.length_append, List.length_singleton]
              have hc : min k ((data h i).length + 1) = min k (data h i).length +
                  if (data h i).length < k then 1 else 0 := by split_ifs <;> omega
              rw [hc]
              by_cases hk : (data h i).length < k
              · simp only [if_pos hk, seen, if_pos hs, mul_one, Nat.cast_add, Nat.cast_one]
                constructor
                · congr 1
                  cases ha : s.2.1 <;> simp [dev, ha, clicked, Bool.and_eq_true, and_comm]
                · trivial
              · simp [hk]
            · have hnc : ¬(s.2.2.2 = true ∧ i = rh h s.2.2.1) := by
                rintro ⟨_, hi⟩
                apply hs
                rw [hi]
                simp
              simp [datum, hs, seen, clicked, hnc]
          let V : Fin n → ℕ → ℝ → List (Step n 1) → ℝ := fun i k u h =>
            Real.exp (u * D i k h - u ^ 2 / 8 * C i k h)
          have hV_step (i : Fin n) (k : ℕ) (u : ℝ) (h : List (Step n 1)) (s : Step n 1) :
              V i k u (h ++ [s]) = V i k u h *
                if (data h i).length < k then Real.exp
                  (u * (if s.2.1 = none then clicked (rh h) i s.2.2 - inst.μ i * seen (rh h) i s.2.2 else 0) -
                    u ^ 2 / 8 * seen (rh h) i s.2.2) else 1 := by
            dsimp only [V]
            rw [(hDC_step i k h s).1, (hDC_step i k h s).2]
            by_cases hk : (data h i).length < k
            · simp only [if_pos hk]
              rw [← Real.exp_add]
              congr 1
              ring
            · simp only [if_neg hk, add_zero, mul_one]
          have hV_mean (i : Fin n) (k : ℕ) (u : ℝ) :
              (∑ τ : Fin T → Step n 1, trajW inst P A T τ * V i k u (List.ofFn τ)) ≤ 1 := by
            have hh := htree_le (V i k u) (by
              intro h
              simp_rw [hV_step, mul_left_comm (K h _), ← Finset.mul_sum]
              by_cases hk : (data h i).length < k
              · simp only [if_pos hk]
                exact (mul_le_mul_of_nonneg_left (hstep_mgf h i u) (Real.exp_pos _).le).trans_eq (mul_one _)
              · simp only [if_neg hk, mul_one, hK_sum, mul_one, le_refl]) T []
            simpa only [List.nil_append, hWmodel, V, D, C, hdata_nil, List.take_nil, List.map_nil,
              List.sum_nil, List.length_nil, Nat.min_zero, Nat.cast_zero, mul_zero, sub_zero, Real.exp_zero] using hh
          let L : ℝ := Real.log (2 * (n : ℝ) * T / farDelta n T)
          have hL : 0 < L := hlog
          have htail (i : Fin n) (k : ℕ) (hk : 1 ≤ k) (σ : ℝ) (hσ : σ ^ 2 = 1) :
              (∑ τ : Fin T → Step n 1, trajW inst P A T τ *
                (if Real.sqrt (L * k) < σ * D i k (List.ofFn τ) then 1 else 0)) ≤ Real.exp (-2 * L) := by
            have hkR : (0 : ℝ) < k := by exact_mod_cast hk
            let b := Real.sqrt (L * k)
            let u := σ * (4 * b / k)
            have hb : 0 < b := Real.sqrt_pos.2 (mul_pos hL hkR)
            have hb2 : b ^ 2 = L * k := Real.sq_sqrt (by positivity)
            have hid : u * (σ * b) - u ^ 2 / 8 * k = 2 * L := by
              dsimp [u]
              field_simp
              ring_nf
              rw [hσ, hb2]
              ring
            have hm := hV_mean i k u
            calc
              _ ≤ Real.exp (-2 * L) * ∑ τ : Fin T → Step n 1,
                  trajW inst P A T τ * V i k u (List.ofFn τ) := by
                rw [Finset.mul_sum]
                apply Finset.sum_le_sum
                intro τ hτ
                by_cases hd : b < σ * D i k (List.ofFn τ)
                · dsimp only [b] at hd
                  simp only [if_pos hd, mul_one]
                  have hC : (C i k (List.ofFn τ) : ℝ) ≤ k := by
                    exact_mod_cast (min_le_left k (data (List.ofFn τ) i).length)
                  have hsq : u ^ 2 = (4 * b / k) ^ 2 := by dsimp [u]; rw [mul_pow, hσ, one_mul]
                  have hex : 2 * L ≤ u * D i k (List.ofFn τ) - u ^ 2 / 8 * C i k (List.ofFn τ) := by
                    have hcoef : 0 < 4 * b / (k : ℝ) := by positivity
                    have hmul := mul_le_mul_of_nonneg_left hd.le hcoef.le
                    have hcomp := mul_le_mul_of_nonneg_left hC (show 0 ≤ u ^ 2 / 8 by positivity)
                    have heq : u * (σ * b) = (4 * b / k) * b := by
                      dsimp [u]
                      calc
                        _ = σ ^ 2 * ((4 * b / k) * b) := by ring
                        _ = _ := by rw [hσ, one_mul]
                    have heq' : u * D i k (List.ofFn τ) = (4 * b / k) * (σ * D i k (List.ofFn τ)) := by dsimp [u]; ring
                    rw [heq] at hid
                    rw [heq']
                    linarith only [hmul, hcomp, hid]
                  have hv : 1 ≤ Real.exp (-2 * L) * V i k u (List.ofFn τ) := by
                    calc
                      1 = Real.exp (-2 * L) * Real.exp (2 * L) := by rw [← Real.exp_add]; simp
                      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hex) (Real.exp_pos _).le
                  have hh := mul_le_mul_of_nonneg_left hv (htraj_nonneg τ)
                  nlinarith only [hh]
                · dsimp only [b] at hd
                  simp only [if_neg hd, mul_zero]
                  exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (htraj_nonneg τ) (Real.exp_pos _).le)
              _ ≤ Real.exp (-2 * L) * 1 := mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
              _ = _ := mul_one _
          have hdata_prefix (h l : List (Step n 1)) (i : Fin n) : data h i <+: data (h ++ l) i := by
            induction l using List.reverseRecOn with
            | nil => simp
            | append_singleton l x ih =>
              rw [← List.append_assoc, hdata_append]
              exact ih.trans (List.prefix_append _ _)
          have hdata_take (h : List (Step n 1)) (t : ℕ) (i : Fin n) :
              (data h i).take (data (h.take t) i).length = data (h.take t) i := by
            have hp := hdata_prefix (h.take t) (h.drop t) i
            rw [List.take_append_drop] at hp
            rcases hp with ⟨l, hl⟩
            rw [← hl]
            simp
          have hB_prefix (h l : List (Step n 1)) : B h ≤ B (h ++ l) := by
            induction l using List.reverseRecOn with
            | nil => simp
            | append_singleton l x ih => rw [← List.append_assoc, hB_append]; omega
          have herror (i : Fin n) (l : List (Bool × Bool)) :
              -((((l.filter (fun z => !z.1)).length : ℕ) : ℝ)) ≤
                (((l.map (fun z => if z.2 then 1 else 0)).sum : ℕ) : ℝ) - inst.μ i * l.length - (l.map (dev i)).sum ∧
              (((l.map (fun z => if z.2 then 1 else 0)).sum : ℕ) : ℝ) - inst.μ i * l.length - (l.map (dev i)).sum ≤
                (((l.filter (fun z => !z.1)).length : ℕ) : ℝ) := by
            induction l with
            | nil => simp
            | cons z l ih =>
              rcases ih with ⟨hlo, hhi⟩
              rcases z with ⟨r, c⟩
              simp [dev] at hlo hhi
              cases r <;> cases c <;> simp [dev, Nat.cast_add] <;>
                constructor <;> linarith only [hlo, hhi, (inst.μ_mem i).1, (inst.μ_mem i).2]
          have hgood_event (τ : Fin T → Step n 1) (hz : trajW inst P A T τ ≠ 0)
              (hg : ∀ (i : Fin n) (k : ℕ), 1 ≤ k → k ≤ T →
                |D i k (List.ofFn τ)| ≤ Real.sqrt (L * k)) : eventE inst T F tb fb τ := by
            have hBfull : B (List.ofFn τ) ≤ F := by
              have hh := hbudget T [] (by simp [hB_nil]) τ (by rwa [hWmodel])
              simpa using hh
            intro t ht htT i
            let h := (List.ofFn τ).take t
            have heq : farStateAt n T F tb fb τ t = st h := rfl
            rw [heq]
            by_cases hc0 : (st h).cnt i = 0
            · exact hzero _ _ hc0
            let k := (st h).cnt i
            have hk : 1 ≤ k := by dsimp [k]; omega
            have hkR : (0 : ℝ) < k := by exact_mod_cast hk
            have hkl : (data h i).length = k := (hstats h i).1.symm
            have hkT : k ≤ T := by
              have hh : k ≤ (ah h).length := (hstate_bounds (ah h) i).2
              have hlen : (ah h).length ≤ t := by simp [ah, h]
              omega
            have hD : D i k (List.ofFn τ) = ((data h i).map (dev i)).sum := by
              dsimp only [D]
              rw [← hkl]
              rw [hdata_take]
            have hd := hg i k hk hkT
            rw [hD, abs_le] at hd
            have hb : B h ≤ F := by
              have hh := hB_prefix ((List.ofFn τ).take t) ((List.ofFn τ).drop t)
              rw [List.take_append_drop] at hh
              exact hh.trans hBfull
            have hf : (((data h i).filter (fun z => !z.1)).length : ℝ) ≤ F := by
              exact_mod_cast (hfake_data h i).trans hb
            have herr := herror i (data h i)
            rw [hkl, ← (hstats h i).2] at herr
            have hsqrt : Real.sqrt (L * (k : ℝ)) = Real.sqrt (L / k) * k := by
              have ha : 0 ≤ Real.sqrt (L / k) * (k : ℝ) := by positivity
              have ha2 : (Real.sqrt (L / k) * (k : ℝ)) ^ 2 = L * k := by
                rw [mul_pow, Real.sq_sqrt (by positivity)]
                field_simp
                <;> ring
              have hb2 := Real.sq_sqrt (show 0 ≤ L * (k : ℝ) by positivity)
              have hb0 := Real.sqrt_nonneg (L * (k : ℝ))
              nlinarith only [ha, ha2, hb2, hb0]
            have hav : (st h).avg i * k = (st h).clk i := by
              simp only [FarState.avg, if_neg hc0]
              change ((st h).clk i : ℝ) / k * k = _
              exact div_mul_cancel₀ _ hkR.ne'
            have hwin : farWindow n T F (st h) i * k = Real.sqrt (L * k) + F := by
              simp only [farWindow, if_neg hc0, farRadius, add_mul]
              change Real.sqrt (L / k) * k + (F : ℝ) / k * k = _
              rw [div_mul_cancel₀ _ hkR.ne', hsqrt]
            constructor <;> nlinarith only [herr.1, herr.2, hd.1, hd.2, hf, hav, hwin, hkR]
          let bad : Fin n → Fin T → Bool → (Fin T → Step n 1) → Prop := fun i j s τ =>
            Real.sqrt (L * (↑((j : ℕ) + 1) : ℝ)) < (if s then (1 : ℝ) else -1) * D i ((j : ℕ) + 1) (List.ofFn τ)
          let cost : (Fin T → Step n 1) → ℝ := fun τ =>
            ∑ i : Fin n, ∑ j : Fin T, ∑ s : Bool, if bad i j s τ then 1 else 0
          have hcost_nonneg (τ : Fin T → Step n 1) : 0 ≤ cost τ := by
            dsimp only [cost]
            positivity
          have hcost (τ : Fin T → Step n 1) (hz : trajW inst P A T τ ≠ 0)
              (he : ¬eventE inst T F tb fb τ) : 1 ≤ cost τ := by
            have hex : ∃ (i : Fin n) (j : Fin T) (s : Bool), bad i j s τ := by
              by_contra! hh
              apply he
              apply hgood_event τ hz
              intro i k hk hkT
              let j : Fin T := ⟨k - 1, by omega⟩
              have hj : (j : ℕ) + 1 = k := by dsimp [j]; omega
              have hpos := hh i j true
              have hneg := hh i j false
              simp only [bad, hj, Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul, not_lt] at hpos hneg
              exact abs_le.mpr ⟨by linarith, hpos⟩
            rcases hex with ⟨i, j, s, hs⟩
            have hinner : (1 : ℝ) ≤ ∑ s' : Bool, if bad i j s' τ then 1 else 0 := by
              have hh := Finset.single_le_sum (s := (Finset.univ : Finset Bool))
                (f := fun s' => if bad i j s' τ then (1 : ℝ) else 0)
                (fun _ _ => by positivity) (Finset.mem_univ s)
              simpa only [if_pos hs] using hh
            have hmid : (∑ s' : Bool, if bad i j s' τ then (1 : ℝ) else 0) ≤
                ∑ j' : Fin T, ∑ s' : Bool, if bad i j' s' τ then 1 else 0 := by
              apply Finset.single_le_sum (fun _ _ => by positivity) (Finset.mem_univ j)
            have houter : (∑ j' : Fin T, ∑ s' : Bool, if bad i j' s' τ then (1 : ℝ) else 0) ≤ cost τ := by
              apply Finset.single_le_sum (fun _ _ => by positivity) (Finset.mem_univ i)
            exact hinner.trans (hmid.trans houter)
          have hcost_mean : (∑ τ : Fin T → Step n 1, trajW inst P A T τ * cost τ) ≤
              2 * n * T * Real.exp (-2 * L) := by
            have hh (i : Fin n) (j : Fin T) (s : Bool) :
                (∑ τ : Fin T → Step n 1, trajW inst P A T τ *
                  if bad i j s τ then 1 else 0) ≤ Real.exp (-2 * L) := by
              have hs : (if s then (1 : ℝ) else -1) ^ 2 = 1 := by cases s <;> norm_num
              exact htail i ((j : ℕ) + 1) (by omega) _ hs
            calc
              _ = ∑ i : Fin n, ∑ j : Fin T, ∑ s : Bool,
                  ∑ τ : Fin T → Step n 1, trajW inst P A T τ * (if bad i j s τ then 1 else 0) := by
                simp only [cost, Finset.mul_sum]
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro i hi
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro j hj
                rw [Finset.sum_comm]
              _ ≤ ∑ _i : Fin n, ∑ _j : Fin T, ∑ _s : Bool, Real.exp (-2 * L) := by
                exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun s _ => hh i j s)))
              _ = _ := by simp; ring
          have hbad_mean : (∑ τ : Fin T → Step n 1,
              trajW inst P A T τ * (if eventE inst T F tb fb τ then 0 else 1)) ≤
              2 * n * T * Real.exp (-2 * L) := by
            apply le_trans _ hcost_mean
            apply Finset.sum_le_sum
            intro τ hτ
            by_cases he : eventE inst T F tb fb τ
            · simp only [if_pos he, mul_zero]
              exact mul_nonneg (htraj_nonneg τ) (hcost_nonneg τ)
            · simp only [if_neg he, mul_one]
              by_cases hz : trajW inst P A T τ = 0
              · simp [hz]
              · exact le_mul_of_one_le_right (htraj_nonneg τ) (hcost τ hz he)
          have hpartition : prob inst P A T (eventE inst T F tb fb) +
              (∑ τ : Fin T → Step n 1, trajW inst P A T τ * (if eventE inst T F tb fb τ then 0 else 1)) = 1 := by
            calc
              _ = ∑ τ : Fin T → Step n 1, trajW inst P A T τ := by
                unfold prob expect
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro τ hτ
                dsimp only
                split_ifs <;> ring
              _ = 1 := hmass
          have hsmall : 2 * (n : ℝ) * T * Real.exp (-2 * L) ≤ farDelta n T ^ 2 / ((n : ℝ) * T) := by
            have hx : 0 < 2 * ((n : ℝ) * T) ^ 2 := by positivity
            have he : Real.exp (-2 * L) = (2 * ((n : ℝ) * T) ^ 2)⁻¹ ^ 2 := by
              have hLdef : L = Real.log (2 * ((n : ℝ) * T) ^ 2) := by dsimp [L]; rw [harg]
              rw [hLdef, show (-2 : ℝ) * Real.log (2 * ((n : ℝ) * T) ^ 2) =
                -(Real.log (2 * ((n : ℝ) * T) ^ 2) + Real.log (2 * ((n : ℝ) * T) ^ 2)) by ring,
                Real.exp_neg, Real.exp_add, Real.exp_log hx]
              field_simp
            have hid : 2 * (n : ℝ) * T * Real.exp (-2 * L) =
                (farDelta n T ^ 2 / ((n : ℝ) * T)) / 2 := by
              rw [he]
              unfold farDelta
              field_simp
              <;> ring
            rw [hid]
            have heps : 0 ≤ farDelta n T ^ 2 / ((n : ℝ) * T) := by positivity
            linarith
          change 1 - farDelta n T ^ 2 / ((n : ℝ) * T) ≤ prob inst P A T (eventE inst T F tb fb)
          linarith
