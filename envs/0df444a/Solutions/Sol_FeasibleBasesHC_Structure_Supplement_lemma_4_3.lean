-- Prove2me | solution 1 for FeasibleBasesHC.Structure.Supplement.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:27:22.751012+00:00
-- url     : https://prove2.me/submissions/97d2febb-5098-4e47-99a4-e67b1890dbe1

import Mathlib
import Definitions.Def_FeasibleBasesHC_Structure_Supplement_Quadruple

open FeasibleBasesHC
open FeasibleBasesHC.Structure
open FeasibleBasesHC.Structure.Supplement

theorem solution {n : ℕ} [NeZero n] (q : Quadruple n)
    (hfeas : q.Feasible) :
    q.U.card = (n - 2) / 2 ∧ q.L.card = (n - 1) / 2 := by
      classical
      have hcardpart0 : q.L.card + q.U.card = n - 2 := by
        have h := congrArg Finset.card q.partition
        rw [Finset.card_union_of_disjoint q.disjoint] at h
        rw [h, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
          Finset.card_pair (Ne.symm q.s_ne_root)]
      have hn1 : n ≠ 1 := by
        rintro rfl
        exact q.s_ne_root (Subsingleton.elim _ _)
      have key3 : ∀ t c d : Fin 3, c ≠ t + 1 → c ≠ t + 1 + 1 → d ≠ t + 1 + 1 → d ≠ t + 1 → d ≠ c → False := by
        decide
      have dist3 : ∀ t : Fin 3, t + 1 ≠ t ∧ t + 1 + 1 ≠ t ∧ t + 1 + 1 ≠ t + 1 := by decide
      have hn3 : n ≠ 3 := by
        rintro rfl
        have hpt : q.pi (q.s - 1) = q.s - 1 + 1 := (q.successor_iff (q.s - 1)).2 rfl
        obtain ⟨d1, d2, d3⟩ := dist3 (q.s - 1)
        refine key3 (q.s - 1) (q.pi (q.s - 1 + 1)) (q.pi (q.s - 1 + 1 + 1)) ?_ ?_ ?_ ?_ ?_
        · intro h; exact d1 (q.pi.injective (h.trans hpt.symm))
        · intro h; exact d1 ((q.successor_iff _).1 h)
        · exact q.fixedPointFree _
        · intro h; exact d2 (q.pi.injective (h.trans hpt.symm))
        · exact q.pi.injective.ne d3
      by_cases hsmall : n ≤ 2
      · constructor <;> omega
      have hn4 : 4 ≤ n := by omega
      obtain ⟨G, hsub, hult⟩ := hfeas
      have hpairpos : ∀ (k : ℕ) (b : ℝ), 2 ≤ k → 0 < b → b < 1 →
          0 < (k:ℝ) * b + k * b ^ (2*k) - ∑ i ∈ Finset.range (2*k), b ^ (i+1) := by
        intro k b hk2 hb0 hb1
        have hpair : ∑ i ∈ Finset.range (2*k), b ^ (i+1) = ∑ i ∈ Finset.range k, (b^(i+1) + b^(2*k-i)) := by
          rw [two_mul, Finset.sum_range_add, Finset.sum_add_distrib]
          congr 1
          rw [← Finset.sum_range_reflect]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mem_range] at hi
          congr 1; omega
        have hD : (k:ℝ) * b + k * b ^ (2*k) - ∑ i ∈ Finset.range (2*k), b ^ (i+1)
            = ∑ i ∈ Finset.range k, (1 - b^i) * (b - b^(2*k-i)) := by
          rw [hpair]
          have : ∀ i ∈ Finset.range k, (1 - b^i) * (b - b^(2*k-i)) = (b + b^(2*k)) - (b^(i+1) + b^(2*k-i)) := by
            intro i hi
            rw [Finset.mem_range] at hi
            have : b^i * b^(2*k-i) = b^(2*k) := by rw [← pow_add]; congr 1; omega
            rw [pow_succ]; linear_combination this
          rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, Finset.sum_add_distrib]
          simp
        rw [hD]
        have hterm0 : ∀ i ∈ Finset.range k, 0 ≤ (1 - b^i) * (b - b^(2*k-i)) := by
          intro i hi
          rw [Finset.mem_range] at hi
          apply mul_nonneg
          · linarith [pow_le_one₀ hb0.le hb1.le (n := i)]
          · have : b^(2*k-i) ≤ b^1 := pow_le_pow_of_le_one hb0.le hb1.le (by omega)
            linarith [pow_one b]
        apply lt_of_lt_of_le _ (Finset.single_le_sum hterm0 (Finset.mem_range.2 (by omega : 1 < k)))
        apply mul_pos
        · simp; linarith
        · have : b^(2*k-1) ≤ b^2 := pow_le_pow_of_le_one hb0.le hb1.le (by omega)
          nlinarith
      have harith1 : ∀ N L P : ℝ, 4 ≤ N → 2 * P = (N - 2) * (N - 1 - 2 * L) + 2 → 1/2 < P → N ≤ 2 * L → False := by
        intro N L P hN hP hP1 hL
        nlinarith [mul_nonneg (sub_nonneg.2 hL) (by linarith : (0:ℝ) ≤ N - 2)]
      have harith2 : ∀ N L P : ℝ, 4 ≤ N → 2 * P = (N - 2) * (N - 1 - 2 * L) + 2 → P < N - 1/2 → 2 * L + 4 ≤ N → False := by
        intro N L P hN hP hP1 hL
        nlinarith [mul_nonneg (sub_nonneg.2 hL) (by linarith : (0:ℝ) ≤ N - 2)]
      have hcardpart : q.L.card + q.U.card = n - 2 := by
        have h := congrArg Finset.card q.partition
        rw [Finset.card_union_of_disjoint q.disjoint] at h
        rw [h, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
          Finset.card_pair (Ne.symm q.s_ne_root)]
      obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ → ℝ, g = fun m b => ∑ k ∈ Finset.range m, b ^ k := ⟨_, rfl⟩
      have hgcont : ∀ m, Continuous (g m) := by intro m; rw [hg]; fun_prop
      have hg1 : ∀ m, g m 1 = m := by intro m; rw [hg]; simp
      have hgmul : ∀ m b, (1 - b) * g m b = 1 - b ^ m := by
        intro m b; rw [hg]; simp only
        have := geom_sum_mul b m
        linear_combination -this
      obtain ⟨Ps, hPs⟩ : ∃ Ps : ℝ → ℝ, Ps = fun b => ∑ k ∈ Finset.range (n - 1), g (k + 1) b
          - (q.L.card : ℝ) * g (n - 1) b - (q.U.card : ℝ) := ⟨_, rfl⟩
      have hPscont : Continuous Ps := by rw [hPs]; fun_prop
      have hev : ∀ (F : ℝ → ℝ), Continuous F → ∀ᶠ b in nhdsWithin (1:ℝ) (Set.Iio 1), |F b - F 1| < 1/2 := by
        intro F hF
        have := (hF.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Iio 1))
        have h2 := Metric.tendsto_nhds.1 this (1/2) (by norm_num)
        filter_upwards [h2] with b hb
        rwa [Real.dist_eq] at hb
      have hevA := hev (fun b => g (n - 1) b - Ps b) ((hgcont _).sub hPscont)
      have hevB := hev (fun b => b * g (n - 2) b - (g (n - 1) b - Ps b))
        ((continuous_id.mul (hgcont _)).sub ((hgcont _).sub hPscont))
      have hflow : ∀ (G : Digraph n) (x : Fin n × Fin n → ℝ),
          ∑ i, outflow G x i = ∑ i, inflow G x i := by
        intro G x
        unfold outflow inflow
        rw [Finset.sum_fiberwise G.E (fun e => e.1) x, Finset.sum_fiberwise G.E (fun e => e.2) x]
      have hys : ∀ (G : Digraph n) (beta : ℝ) (x : Fin n × Fin n → ℝ) (y : Fin n → ℝ),
          WHCore G beta x y → (∀ i ∈ q.L, y i = 0) → (∀ i ∈ q.U, y i = beta - beta ^ (n - 1)) →
          (1 - beta) * (1 + (n - 1 : ℝ) * beta ^ (n - 1) + q.U.card * (beta - beta ^ (n - 1))
            + y q.s) = 1 - beta ^ n := by
        intro G beta x y hc hL hU
        obtain ⟨-, hy0, hbal, hout⟩ := hc
        have h1 : ∑ i, (outflow G x i - beta * inflow G x i) = 1 - beta ^ n := by
          rw [Finset.sum_congr rfl (fun i _ => hbal i)]
          simp
        have h2 : ∑ i, outflow G x i = 1 + (n - 1 : ℝ) * beta ^ (n - 1)
            + q.U.card * (beta - beta ^ (n - 1)) + y q.s := by
          have : ∀ i, outflow G x i = (if i = 0 then 1 else beta ^ (n - 1)) + (if i = 0 then 0 else y i) := by
            intro i; have := hout i; linarith
          rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib]
          have hA : ∑ i : Fin n, (if i = 0 then (1:ℝ) else beta ^ (n - 1)) = 1 + (n - 1 : ℝ) * beta ^ (n - 1) := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
            rw [Finset.sum_congr rfl (fun i hi => if_neg (Finset.ne_of_mem_erase hi))]
            simp only [if_true, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            have : 1 ≤ n := NeZero.one_le
            push_cast [this]; ring
          have hB : ∑ i : Fin n, (if i = 0 then (0:ℝ) else y i) = q.U.card * (beta - beta ^ (n - 1)) + y q.s := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
            rw [Finset.sum_congr rfl (fun i hi => if_neg (Finset.ne_of_mem_erase hi))]
            have hpart : Finset.univ.erase (0 : Fin n) = (q.L ∪ q.U) ∪ {q.s} := by
              rw [q.partition]; ext i; simp only [Finset.mem_erase, Finset.mem_univ, Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
              by_cases h : i = q.s <;> simp [h, q.s_ne_root]
            have hdisj : Disjoint (q.L ∪ q.U) {q.s} := by
              rw [q.partition]; simp
            rw [hpart, Finset.sum_union hdisj, Finset.sum_union q.disjoint,
              Finset.sum_congr rfl hL, Finset.sum_congr rfl hU]
            simp; ring
          rw [hA, hB]; ring
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← hflow G x] at h1
        rw [← h2]; linarith
      have hult' : ∀ᶠ beta : ℝ in nhdsWithin (1:ℝ) (Set.Iio 1), q.basis ∈ Gam G beta := hult
      obtain ⟨b, hGam, hA, hB⟩ := (hult'.and (hevA.and hevB)).exists
      obtain ⟨hb0, hb1, x, y, ⟨hshape, hind, hcore, hxA, hyL, hyU⟩, ⟨-, hxnn, hybd⟩⟩ := hGam
      have hY := hys G b x y hcore hyL hyU
      obtain ⟨hxG, hy0, hbal, hout⟩ := hcore
      have hYbd := hybd q.s q.s_ne_root
      have hsumn : 1 - b ^ n = (1 - b) * (1 + ∑ k ∈ Finset.range (n-1), b^(k+1)) := by
        have := hgmul n b
        rw [hg] at this; simp only at this
        have e : ∑ k ∈ Finset.range n, b^k = 1 + ∑ k ∈ Finset.range (n-1), b^(k+1) := by
          obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n-1, by omega⟩
          rw [hm, Finset.sum_range_succ']; simp; ring
        rw [← this, e]
      have hcastLU : (q.L.card : ℝ) + q.U.card = n - 2 := by
        have : q.L.card + q.U.card + 2 = n := by omega
        have : ((q.L.card + q.U.card + 2 : ℕ) : ℝ) = n := by exact_mod_cast this
        push_cast at this; linarith
      have h1b : (1 - b) ≠ 0 := by intro h; linarith
      have hyform : y q.s = ∑ k ∈ Finset.range (n-1), b^(k+1) - (q.L.card + 1) * b^(n-1) - q.U.card * b := by
        rw [hsumn] at hY
        have h := mul_left_cancel₀ h1b hY
        linear_combination h + b^(n-1) * hcastLU
      have hPsid : (1 - b) * Ps b = 1 - b ^ (n-1) - y q.s := by
        have h1 : ((n - 1 : ℕ) : ℝ) = n - 1 := by rw [Nat.cast_sub (by omega)]; simp
        have e1 : (1 - b) * ∑ k ∈ Finset.range (n - 1), g (k + 1) b = ((n-1 : ℕ):ℝ) - ∑ k ∈ Finset.range (n-1), b^(k+1) := by
          rw [Finset.mul_sum, Finset.sum_congr rfl (fun k _ => hgmul (k+1) b), Finset.sum_sub_distrib]; simp
        rw [h1] at e1
        have e2 := hgmul (n-1) b
        rw [hPs]; simp only
        rw [hyform]
        linear_combination e1 - (q.L.card:ℝ) * e2 - hcastLU
      have hba : b ^ (n - 1) = b * b ^ (n - 2) := by rw [← pow_succ']; congr 1; omega
      have hG1 := hgmul (n - 1) b
      have hG2 := hgmul (n - 2) b
      have hyQ : y q.s = (1 - b) * (g (n - 1) b - Ps b) := by
        linear_combination hPsid - hG1
      have h1b' : 0 < 1 - b := by linarith
      have hy_lo : 0 ≤ g (n - 1) b - Ps b := by
        by_contra h; push_neg at h
        have := mul_neg_of_pos_of_neg h1b' h; linarith [hYbd.1]
      have hy_hi : g (n - 1) b - Ps b ≤ b * g (n - 2) b := by
        by_contra h; push_neg at h
        have h2 : (1 - b) * (b * g (n - 2) b) < (1 - b) * (g (n - 1) b - Ps b) :=
          mul_lt_mul_of_pos_left h h1b'
        have h3 : (1 - b) * (b * g (n - 2) b) = b - b ^ (n - 1) := by
          rw [hba]; linear_combination b * hG2
        linarith [hYbd.2]
      have hgauss : ∀ m : ℕ, 2 * ∑ k ∈ Finset.range m, ((k:ℝ) + 1) = m * (m + 1) := by
        intro m; induction m with
        | zero => simp
        | succ m ih => rw [Finset.sum_range_succ]; push_cast; linear_combination ih
      have hn1R : ((n - 1 : ℕ) : ℝ) = n - 1 := by rw [Nat.cast_sub (by omega)]; simp
      have hn2R : ((n - 2 : ℕ) : ℝ) = n - 2 := by rw [Nat.cast_sub (by omega)]; simp
      have hPs1 : 2 * Ps 1 = ((n:ℝ) - 1) * n - 2 * q.L.card * (n - 1) - 2 * q.U.card := by
        have := hgauss (n - 1)
        rw [hn1R] at this
        rw [hPs]; simp only [hg1, hn1R]; push_cast
        linear_combination this
      have hA' : |(g (n - 1) b - Ps b) - (((n:ℝ) - 1) - Ps 1)| < 1/2 := by
        simpa [hg1, hn1R] using hA
      have hB' : |(b * g (n - 2) b - (g (n - 1) b - Ps b)) - (((n:ℝ) - 2) - (((n:ℝ) - 1) - Ps 1))| < 1/2 := by
        simpa [hg1, hn1R, hn2R] using hB
      have hPsr : 1/2 < Ps 1 ∧ Ps 1 < n - 1/2 := by
        constructor
        · have := (abs_lt.1 hB').2; linarith
        · have := (abs_lt.1 hA').2; linarith
      have hnR : (4:ℝ) ≤ n := by exact_mod_cast hn4
      have hPs1' : 2 * Ps 1 = ((n:ℝ) - 2) * ((n:ℝ) - 1 - 2 * q.L.card) + 2 := by
        linear_combination hPs1 - 2 * hcastLU
      have hl1 : 2 * q.L.card + 1 ≤ n := by
        by_contra h; push_neg at h
        have h' : (n:ℝ) ≤ 2 * q.L.card := by exact_mod_cast (by omega : n ≤ 2 * q.L.card)
        exact harith1 _ _ _ hnR hPs1' hPsr.1 h'
      have hl2 : n ≤ 2 * q.L.card + 3 := by
        by_contra h; push_neg at h
        have h' : 2 * (q.L.card:ℝ) + 4 ≤ n := by exact_mod_cast (by omega : 2 * q.L.card + 4 ≤ n)
        exact harith2 _ _ _ hnR hPs1' hPsr.2 h'
      have hcards : q.U.card = (n - 2) / 2 ∧ q.L.card = (n - 1) / 2 := by
        rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
        · constructor <;> omega
        · by_cases hlm : q.L.card = m
          · constructor <;> omega
          · exfalso
            have hl : q.L.card + 1 = m := by omega
            have hu : q.U.card = m := by omega
            have hm2 : 2 ≤ m := by omega
            have hn1 : n - 1 = 2 * m := by omega
            have := hpairpos m b hm2 hb0 hb1
            rw [hn1] at hyform
            have hlR : (q.L.card : ℝ) + 1 = m := by exact_mod_cast hl
            have huR : (q.U.card : ℝ) = m := by exact_mod_cast hu
            rw [hlR, huR] at hyform
            linarith [hYbd.1]

      exact hcards
