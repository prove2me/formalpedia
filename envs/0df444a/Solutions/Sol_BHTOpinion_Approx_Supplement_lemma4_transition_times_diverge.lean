-- Prove2me | solution 1 for BHTOpinion.Approx.Supplement.lemma4_transition_times_diverge
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:14:33.185987+00:00
-- url     : https://prove2.me/submissions/d2c8b596-1b53-4978-a07c-7aab61a88faf

import Mathlib
import Definitions.Def_BHTOpinion_Approx_Discrete
import Definitions.Def_BHTOpinion_Approx_Supplement_Cells

open BHTOpinion
open BHTOpinion.Approx
open BHTOpinion.Approx.Supplement

theorem solution {n : ℕ} (x₀ : Fin n → ℝ) (G : ℕ → SimpleGraph (Fin n))
    (t : ℕ → ℝ) (x : ℝ → Fin n → ℝ) (hrun : IsCellRun x₀ G t x)
    (hnp : ∀ k : ℕ, IsNonproblematicSwitch (G k) (G (k + 1)) (x (t (k + 1)))) :
    Filter.Tendsto t Filter.atTop Filter.atTop ∧
      (BHTOpinion.Approx.IsDiscreteSolution x ∧
        ∀ y : ℝ → Fin n → ℝ, BHTOpinion.Approx.IsDiscreteSolution y → y 0 = x₀ →
          ∀ s : ℝ, 0 ≤ s → y s = x s) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ T : ℝ, ∃ s : ℝ, T ≤ s ∧ ∃ v : Fin n → ℝ, HasDerivAt x v s ∧ ε < ‖v‖ := by
        set_option maxHeartbeats 4000000 in
          classical
          have hstep : ∀ k, t k < t (k + 1) := fun k => hrun.increasing (Nat.lt_succ_self k)
          let L : SimpleGraph (Fin n) → (Fin n → ℝ) → Fin n → ℝ :=
            fun H p i => ∑ j, if H.Adj i j then p i - p j else 0
          let E : (Fin n → ℝ) → ℝ := fun p => ∑ i, (p i) ^ 2
          let W : SimpleGraph (Fin n) → (Fin n → ℝ) → ℝ :=
            fun H p => ∑ i, ∑ j, if H.Adj i j then (p i - p j) ^ 2 else 0
          let C : ℝ := 4 * (n : ℝ) ^ 2
          have hL : ∀ H p i, frozenField H p i = -L H p i := by
            intro H p i
            simp only [frozenField, Pi.neg_apply, SimpleGraph.lapMatrix_mulVec_apply]
            congr 1
            dsimp [L]
            rw [← Finset.sum_filter]
            have heq : Finset.univ.filter (fun j => H.Adj i j) = H.neighborFinset i := by
              ext j
              simp
            rw [heq, Finset.sum_sub_distrib]
            simp [SimpleGraph.card_neighborFinset_eq_degree]
          have hLneg : ∀ H p i, L H (-p) i = - L H p i := by
            intro H p i
            dsimp [L]
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro j hj
            split_ifs <;> simp <;> ring
          have hWbound : ∀ H p, W H p ≤ 4 * (n : ℝ) * E p := by
            intro H p
            calc
              W H p ≤ ∑ i : Fin n, ∑ j : Fin n, (2 * (p i) ^ 2 + 2 * (p j) ^ 2) := by
                apply Finset.sum_le_sum
                intro i hi
                apply Finset.sum_le_sum
                intro j hj
                split_ifs <;> nlinarith [sq_nonneg (p i + p j), sq_nonneg (p i), sq_nonneg (p j)]
              _ = 4 * (n : ℝ) * E p := by
                simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
                  Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
                dsimp [E]
                ring
          have hLbound : ∀ H p, E (L H p) ≤ (n : ℝ) * W H p := by
            intro H p
            calc
              E (L H p) ≤ ∑ i : Fin n, (n : ℝ) *
                  ∑ j : Fin n, if H.Adj i j then (p i - p j) ^ 2 else 0 := by
                apply Finset.sum_le_sum
                intro i hi
                dsimp [L]
                have hb := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
                  (f := fun j => if H.Adj i j then p i - p j else 0)
                simpa only [Finset.card_univ, Fintype.card_fin, ite_pow, zero_pow (by decide : 2 ≠ 0)] using hb
              _ = (n : ℝ) * W H p := by simp [W, Finset.mul_sum]
          have hLEbound : ∀ H p, E (L H p) ≤ C * E p := by
            intro H p
            have ha := hLbound H p
            have hb := mul_le_mul_of_nonneg_left (hWbound H p) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
            dsimp [C]
            nlinarith
          have hWLbound : ∀ H p, W H (L H p) ≤ C * W H p := by
            intro H p
            have ha := hWbound H (L H p)
            have hb := mul_le_mul_of_nonneg_left (hLbound H p) (by positivity : (0 : ℝ) ≤ 4 * (n : ℝ))
            dsimp [C]
            nlinarith
          have henergy : ∀ H p, 2 * (∑ i, p i * L H p i) = W H p := by
            intro H p
            have hswap : (∑ i : Fin n, ∑ j : Fin n,
                if H.Adj i j then p j * (p j - p i) else 0) =
                ∑ i : Fin n, ∑ j : Fin n, if H.Adj i j then p i * (p i - p j) else 0 := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              rw [H.adj_comm]
            have hsum : (∑ i, p i * L H p i) =
                ∑ i : Fin n, ∑ j : Fin n, if H.Adj i j then p i * (p i - p j) else 0 := by
              apply Finset.sum_congr rfl
              intro i hi
              dsimp [L]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              split_ifs <;> simp
            rw [hsum]
            calc
              2 * (∑ i : Fin n, ∑ j : Fin n, if H.Adj i j then p i * (p i - p j) else 0) =
                  (∑ i : Fin n, ∑ j : Fin n, if H.Adj i j then p i * (p i - p j) else 0) +
                  (∑ i : Fin n, ∑ j : Fin n, if H.Adj i j then p j * (p j - p i) else 0) := by rw [hswap]; ring
              _ = W H p := by
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro i hi
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro j hj
                split_ifs <;> ring
          have hDL : ∀ (H : SimpleGraph (Fin n)) (f : ℝ → Fin n → ℝ) (v : Fin n → ℝ)
              (s : Set ℝ) (a : ℝ), HasDerivWithinAt f v s a →
              HasDerivWithinAt (fun u => L H (f u)) (L H v) s a := by
            intro H f v s a hf
            apply hasDerivWithinAt_pi.mpr
            intro i
            apply HasDerivWithinAt.fun_sum
            intro j hj
            by_cases hij : H.Adj i j
            · simpa only [if_pos hij, Pi.sub_apply] using
                ((hasDerivWithinAt_pi.mp hf i).fun_sub (hasDerivWithinAt_pi.mp hf j))
            · simpa only [if_neg hij] using (hasDerivWithinAt_const a s (0 : ℝ))
          have hDE : ∀ (f : ℝ → Fin n → ℝ) (v : Fin n → ℝ) (s : Set ℝ) (a : ℝ),
              HasDerivWithinAt f v s a →
              HasDerivWithinAt (fun u => E (f u)) (2 * ∑ i, f a i * v i) s a := by
            intro f v s a hf
            have hh := HasDerivWithinAt.fun_sum (u := (Finset.univ : Finset (Fin n)))
              (fun i hi => (hasDerivWithinAt_pi.mp hf i).fun_pow 2)
            simpa only [E, Nat.cast_ofNat, Nat.reduceSub, pow_one, ← Finset.mul_sum, mul_assoc] using hh
          let Q : SimpleGraph (Fin n) → (Fin n → ℝ) → ℝ :=
            fun H p => C * E p - E (L H p)
          have hQpos : ∀ H p, 0 ≤ Q H p := by
            intro H p
            exact sub_nonneg.mpr (hLEbound H p)
          have hQderiv : ∀ k a, a ∈ Set.Icc (t k) (t (k + 1)) →
              HasDerivWithinAt (fun u => Q (G k) (x u))
                (W (G k) (L (G k) (x a)) - C * W (G k) (x a))
                (Set.Icc (t k) (t (k + 1))) a := by
            intro k a ha
            have hf : HasDerivWithinAt x (fun i => -L (G k) (x a) i)
                (Set.Icc (t k) (t (k + 1))) a := by
              convert hrun.flow k a ha using 1
              ext i
              exact (hL (G k) (x a) i).symm
            have he := hDE x _ _ _ hf
            have hl := hDL (G k) x _ _ _ hf
            have hev : 2 * (∑ i, x a i * (-L (G k) (x a) i)) = -W (G k) (x a) := by
              simp only [mul_neg, Finset.sum_neg_distrib, mul_neg]
              rw [henergy]
            have hlev : L (G k) (fun i => -L (G k) (x a) i) =
                fun i => -L (G k) (L (G k) (x a)) i := by
              ext i
              exact hLneg (G k) (L (G k) (x a)) i
            rw [hev] at he
            rw [hlev] at hl
            have hel := hDE (fun u => L (G k) (x u)) _ _ _ hl
            have hvel : 2 * (∑ i, L (G k) (x a) i * (-L (G k) (L (G k) (x a)) i)) =
                -W (G k) (L (G k) (x a)) := by
              simp only [mul_neg, Finset.sum_neg_distrib, mul_neg]
              rw [henergy]
            rw [hvel] at hel
            convert (he.const_mul C).fun_sub hel using 1 <;> first | rfl | ring
          have hQmono : ∀ k, AntitoneOn (fun u => Q (G k) (x u)) (Set.Icc (t k) (t (k + 1))) := by
            intro k
            apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
            · intro a ha
              exact (hQderiv k a ha).continuousWithinAt
            · intro a ha
              rw [interior_Icc] at ha
              exact (hQderiv k a ⟨ha.1.le, ha.2.le⟩).mono (by
                rw [interior_Icc]
                exact Set.Ioo_subset_Icc_self)
            · intro a ha
              exact sub_nonpos.mpr (hWLbound (G k) (x a))
          have hclosure : ∀ (H : SimpleGraph (Fin n)) p, p ∈ closure (cell H) →
              ∀ i j, i ≠ j →
              (H.Adj i j → (p i - p j) ^ 2 ≤ 1) ∧
              (¬H.Adj i j → 1 ≤ (p i - p j) ^ 2) := by
            intro H p hp i j hij
            have hc : Continuous (fun p : Fin n → ℝ => (p i - p j) ^ 2) :=
              ((continuous_apply i).sub (continuous_apply j)).pow 2
            constructor
            · intro he
              apply closure_minimal (t := {p : Fin n → ℝ | (p i - p j) ^ 2 ≤ 1}) ?_ (isClosed_le hc continuous_const) hp
              intro q hq
              have hh := (abs_lt.mp ((hq i j hij).1 he))
              dsimp
              nlinarith
            · intro he
              apply closure_minimal (t := {p : Fin n → ℝ | 1 ≤ (p i - p j) ^ 2}) ?_ (isClosed_le continuous_const hc) hp
              intro q hq
              have hh := (hq i j hij).2 he
              dsimp
              rcases le_total 0 (q i - q j) with h | h
              · rw [abs_of_nonneg h] at hh
                nlinarith
              · rw [abs_of_nonpos h] at hh
                nlinarith
          have hleftmax : ∀ (f : ℝ → ℝ) (d a b : ℝ), a < b →
              HasDerivWithinAt f d (Set.Icc a b) b →
              (∀ u ∈ Set.Ioo a b, f u ≤ f b) → 0 ≤ d := by
            intro f d a b hab hd hm
            have ht := hasDerivWithinAt_iff_tendsto_slope.mp (hd.mono Set.Ioo_subset_Icc_self)
            have hdiff : Set.Ioo a b \ {b} = Set.Ioo a b := by ext u; simp
            rw [hdiff] at ht
            have : (nhdsWithin b (Set.Ioo a b)).NeBot := by
              rw [nhdsWithin_Ioo_eq_nhdsLT hab]
              infer_instance
            apply ge_of_tendsto ht
            filter_upwards [self_mem_nhdsWithin] with u hu
            rw [slope_def_field]
            exact div_nonneg_of_nonpos (sub_nonpos.mpr (hm u hu)) (sub_nonpos.mpr hu.2.le)
          have hleftmin : ∀ (f : ℝ → ℝ) (d a b : ℝ), a < b →
              HasDerivWithinAt f d (Set.Icc a b) b →
              (∀ u ∈ Set.Ioo a b, f b ≤ f u) → d ≤ 0 := by
            intro f d a b hab hd hm
            have hh := hleftmax (fun u => -f u) (-d) a b hab hd.neg
              (fun u hu => neg_le_neg (hm u hu))
            linarith
          have hupdate : ∀ (H H' : SimpleGraph (Fin n)) (i j : Fin n), i ≠ j →
              symmDiff H.edgeSet H'.edgeSet = {s(i,j)} → ∀ p,
              let d := (if H.Adj i j then (-1 : ℝ) else 1) * (p i - p j)
              E (L H' p) = E (L H p) + 2 * d * (L H p i - L H p j) + 2 * d ^ 2 := by
            intro H H' i j hij hdiff p d
            have hrel : ∀ a b, H'.Adj a b ↔
                if (a = i ∧ b = j) ∨ (a = j ∧ b = i) then ¬H.Adj a b else H.Adj a b := by
              intro a b
              have hm := congrArg (fun S : Set (Sym2 (Fin n)) => s(a,b) ∈ S) hdiff
              simp only [Set.mem_symmDiff, SimpleGraph.mem_edgeSet, Set.mem_singleton_iff, Sym2.eq_iff] at hm
              by_cases hp : (a = i ∧ b = j) ∨ (a = j ∧ b = i)
              · simp only [if_pos hp]
                tauto
              · simp only [if_neg hp]
                tauto
            have hterm : ∀ a b,
                (if H'.Adj a b then p a - p b else 0) =
                (if H.Adj a b then p a - p b else 0) +
                (if a = i ∧ b = j then d else 0) - (if a = j ∧ b = i then d else 0) := by
              intro a b
              by_cases hai : a = i
              · subst a
                by_cases hbj : b = j
                · subst b
                  by_cases he : H.Adj i j <;> simp [hrel, hij, Ne.symm hij, d, he] <;> ring
                · have hab : H'.Adj i b ↔ H.Adj i b := by simpa [hij, hbj] using hrel i b
                  simp [hab, hij, hbj]
              · by_cases haj : a = j
                · subst a
                  by_cases hbi : b = i
                  · subst b
                    by_cases he : H.Adj i j <;> simp [hrel, hij, Ne.symm hij, d, he, H.adj_comm] <;> ring
                  · have hab : H'.Adj j b ↔ H.Adj j b := by simpa [Ne.symm hij, hbi] using hrel j b
                    simp [hab, Ne.symm hij, hbi]
                · have hab : H'.Adj a b ↔ H.Adj a b := by simpa [hai, haj] using hrel a b
                  simp [hab, hai, haj]
            have hvec : ∀ a, L H' p a = L H p a + (if a = i then d else 0) - (if a = j then d else 0) := by
              intro a
              change (∑ b : Fin n, if H'.Adj a b then p a - p b else 0) = _
              calc
                _ = ∑ b : Fin n, ((if H.Adj a b then p a - p b else 0) +
                    (if a = i ∧ b = j then d else 0) - (if a = j ∧ b = i then d else 0)) :=
                  Finset.sum_congr rfl (fun b _ => hterm a b)
                _ = _ := by
                  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
                  by_cases hai : a = i <;> by_cases haj : a = j <;> simp [hai, haj, L, hij, Ne.symm hij]
            calc
              E (L H' p) = ∑ a : Fin n, ((L H p a) ^ 2 +
                  (if a = i then 2 * d * L H p i + d ^ 2 else 0) +
                  (if a = j then -2 * d * L H p j + d ^ 2 else 0)) := by
                apply Finset.sum_congr rfl
                intro a ha
                rw [hvec]
                by_cases hai : a = i
                · subst a
                  simp [hij] <;> ring
                · by_cases haj : a = j
                  · subst a
                    simp [Ne.symm hij] <;> ring
                  · simp [hai, haj]
              _ = E (L H p) + 2 * d * (L H p i - L H p j) + 2 * d ^ 2 := by
                simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
                dsimp [E]
                ring
          have hQjump : ∀ k, Q (G (k + 1)) (x (t (k + 1))) + 2 ≤
              Q (G k) (x (t (k + 1))) := by
            intro k
            obtain ⟨i, j, hij, hdiff, hnpder⟩ := (hnp k).2.2.2
            let p := x (t (k + 1))
            have hxor : (G k).Adj i j ∧ ¬(G (k + 1)).Adj i j ∨
                (G (k + 1)).Adj i j ∧ ¬(G k).Adj i j := by
              have hm : s(i,j) ∈ symmDiff (G k).edgeSet (G (k + 1)).edgeSet := by rw [hdiff]; simp
              simpa only [Set.mem_symmDiff, SimpleGraph.mem_edgeSet] using hm
            have hp : (p i - p j) ^ 2 = 1 := by
              have hc := hclosure (G k) p (hnp k).1 i j hij
              have hc' := hclosure (G (k + 1)) p (hnp k).2.1 i j hij
              rcases hxor with h | h
              · exact le_antisymm (hc.1 h.1) (hc'.2 h.2)
              · exact le_antisymm (hc'.1 h.1) (hc.2 h.2)
            have hf := hrun.flow k (t (k + 1)) ⟨(hstep k).le, le_rfl⟩
            have hq := ((hasDerivWithinAt_pi.mp hf i).fun_sub (hasDerivWithinAt_pi.mp hf j)).fun_pow 2
            have hq' : HasDerivWithinAt (fun u => (x u i - x u j) ^ 2)
                (-2 * (p i - p j) * (L (G k) p i - L (G k) p j))
                (Set.Icc (t k) (t (k + 1))) (t (k + 1)) := by
              convert hq using 1 <;> first | rfl | (simp only [Pi.sub_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, hL]; dsimp [p]; ring)
            have hb := hupdate (G k) (G (k + 1)) i j hij hdiff p
            by_cases he : (G k).Adj i j
            · have hd : 0 ≤ -2 * (p i - p j) * (L (G k) p i - L (G k) p j) := by
                apply hleftmax _ _ _ _ (hstep k) hq'
                intro u hu
                have hh := abs_lt.mp (((hrun.inside k u hu) i j hij).1 he)
                change (x u i - x u j) ^ 2 ≤ (p i - p j) ^ 2
                rw [hp]
                nlinarith
              dsimp only at hb
              rw [if_pos he] at hb
              dsimp [Q]
              change C * E p - E (L (G (k + 1)) p) + 2 ≤ C * E p - E (L (G k) p)
              nlinarith [hp]
            · have hd : -2 * (p i - p j) * (L (G k) p i - L (G k) p j) ≤ 0 := by
                apply hleftmin _ _ _ _ (hstep k) hq'
                intro u hu
                have hh := ((hrun.inside k u hu) i j hij).2 he
                change (p i - p j) ^ 2 ≤ (x u i - x u j) ^ 2
                rw [hp]
                rcases le_total 0 (x u i - x u j) with h | h
                · rw [abs_of_nonneg h] at hh
                  nlinarith
                · rw [abs_of_nonpos h] at hh
                  nlinarith
              dsimp only at hb
              rw [if_neg he] at hb
              dsimp [Q]
              change C * E p - E (L (G (k + 1)) p) + 2 ≤ C * E p - E (L (G k) p)
              nlinarith [hp]
          have hcount : ∀ k, Q (G k) (x (t k)) + 2 * (k : ℝ) ≤ Q (G 0) (x (t 0)) := by
            intro k
            induction k with
            | zero => simp
            | succ k hk =>
              have hm := hQmono k ⟨le_rfl, (hstep k).le⟩ ⟨(hstep k).le, le_rfl⟩ (hstep k).le
              have hj := hQjump k
              push_cast
              change Q (G (k + 1)) (x (t (k + 1))) + 2 * ((k : ℝ) + 1) ≤ _
              linarith
          obtain ⟨k, hk⟩ := exists_nat_gt (Q (G 0) (x (t 0)))
          have hc := hcount k
          have hp := hQpos (G k) (x (t k))
          have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          exfalso
          linarith
