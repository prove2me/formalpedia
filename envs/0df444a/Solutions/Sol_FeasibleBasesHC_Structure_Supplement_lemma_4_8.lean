-- Prove2me | solution 1 for FeasibleBasesHC.Structure.Supplement.lemma_4_8
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:27:53.076749+00:00
-- url     : https://prove2.me/submissions/a59c945c-c880-4823-b128-123decf87d4d

import Mathlib
import Definitions.Def_FeasibleBasesHC_Structure_Supplement_Counts

open FeasibleBasesHC
open FeasibleBasesHC.Structure
open FeasibleBasesHC.Structure.Supplement

theorem solution {n : ℕ} [NeZero n] (q : Quadruple n)
    (hfeas : q.Feasible) :
    (Odd n → q.s - 1 ∈ R n) ∧
    (Even n → q.s - 1 ∈ R n ∪ q.U) := by
      refine ⟨fun hodd => ?_, fun _ => ?_⟩
      · obtain ⟨k, hn⟩ := hodd
        have hcardpart : q.L.card + q.U.card = n - 2 := by
          have h := congrArg Finset.card q.partition
          rw [Finset.card_union_of_disjoint q.disjoint] at h
          rw [h, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
            Finset.card_pair (Ne.symm q.s_ne_root)]
        -- total outflow equals total inflow
        have hflow : ∀ (G : Digraph n) (x : Fin n × Fin n → ℝ),
            ∑ i, outflow G x i = ∑ i, inflow G x i := by
          intro G x
          unfold outflow inflow
          rw [Finset.sum_fiberwise G.E (fun e => e.1) x, Finset.sum_fiberwise G.E (fun e => e.2) x]
        -- the free variable y_s is pinned by the flow balance
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
        have hk2 : 2 ≤ k := by
          by_contra hk
          have hk' : k = 0 ∨ k = 1 := by omega
          have key : ∀ (s : Fin 3), s ≠ 0 → ∀ (pi : Equiv.Perm (Fin 3)),
              (∀ i, pi i ≠ i) → (∀ i, pi i = i + 1 ↔ i = s - 1) → False := by decide
          rcases q with ⟨s, pi, L, U, hs0, hfp, hsucc, -, -⟩
          rcases hk' with rfl | rfl
          · subst hn
            exact hs0 (Fin.ext (by have := s.isLt; simp at this ⊢))
          · subst hn
            exact key s hs0 pi hfp hsucc
        have hmp3 : ∀ G : Digraph n, q.arcs ⊆ G.E → q.basis ∈ GamUlt G →
            (q.U.card = k - 1 ∧ q.L.card = k) ∧ q.pi q.s ∈ q.U ∧ q.s - 1 ∈ R n := by
          intro G hsub hult
          have hΔgen : ∀ b : ℝ, 0 < b → b < 1 → 1 - 1 / (4 * (k:ℝ)^3) < b → 0 < (k:ℝ) * b + k * b ^ (2*k) - ∑ i ∈ Finset.range (2*k), b ^ (i+1) ∧
              (k:ℝ) * b + k * b ^ (2*k) - ∑ i ∈ Finset.range (2*k), b ^ (i+1) < b * (1 - b) := by
              intro b hb0 hb1 hbδ
              have hkR : (2:ℝ) ≤ k := by exact_mod_cast hk2
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
              have hkR : (2:ℝ) ≤ k := by exact_mod_cast hk2
              constructor
              · apply lt_of_lt_of_le _ (Finset.single_le_sum hterm0 (Finset.mem_range.2 (by omega : 1 < k)))
                apply mul_pos
                · simp; linarith
                · have : b^(2*k-1) ≤ b^2 := pow_le_pow_of_le_one hb0.le hb1.le (by omega)
                  nlinarith
              · have hbern : ∀ m : ℕ, 1 - (m:ℝ) * (1 - b) ≤ b^m := by
                  intro m
                  have := one_add_mul_le_pow (a := b - 1) (by linarith) m
                  simp at this; linarith
                have hup : ∀ i ∈ Finset.range k, (1 - b^i) * (b - b^(2*k-i)) ≤ (k * (1-b)) * (2 * k * (1-b)) := by
                  intro i hi
                  rw [Finset.mem_range] at hi
                  apply mul_le_mul
                  · have := hbern i
                    have : (i:ℝ) ≤ k := by exact_mod_cast hi.le
                    nlinarith
                  · have h1 := hbern (2*k)
                    have h2 : b^(2*k) ≤ b^(2*k-i) := pow_le_pow_of_le_one hb0.le hb1.le (by omega)
                    push_cast at h1
                    linarith
                  · have : b^(2*k-i) ≤ b^1 := pow_le_pow_of_le_one hb0.le hb1.le (by omega)
                    linarith [pow_one b]
                  · have : (0:ℝ) ≤ k := by positivity
                    nlinarith
                have hs := Finset.sum_le_sum hup
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
                have hk3 : (0:ℝ) < k^3 := by positivity
                have h1b : 1 - b < 1 / (4 * (k:ℝ)^3) := by linarith
                have : (k:ℝ)^3 * (1 - b) < 1/4 := by
                  rw [lt_div_iff₀ (by positivity)] at h1b; nlinarith
                have hb12 : (1:ℝ)/2 < b := by
                  have : 1 / (4 * (k:ℝ)^3) ≤ 1/2 := by
                    have h8 : (2:ℝ)^3 ≤ (k:ℝ)^3 := pow_le_pow_left₀ (by norm_num) hkR 3
                    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
                  linarith
                calc _ ≤ (k:ℝ) * ((k * (1-b)) * (2 * k * (1-b))) := hs
                  _ = 2 * ((k:ℝ)^3 * (1 - b)) * (1 - b) := by ring
                  _ < b * (1 - b) := by nlinarith
          have hδ : (0:ℝ) < 1 / (4 * (k:ℝ)^3) := by positivity
          have hev : ∀ᶠ beta : ℝ in nhdsWithin (1:ℝ) (Set.Iio 1), 1 - 1 / (4 * (k:ℝ)^3) < beta :=
            eventually_nhdsWithin_of_eventually_nhds (isOpen_Ioi.mem_nhds (by show (1:ℝ) - _ < 1; linarith))
          have hult' : ∀ᶠ beta : ℝ in nhdsWithin (1:ℝ) (Set.Iio 1), q.basis ∈ Gam G beta := hult
          obtain ⟨b, hGam, hbδ⟩ := (hult'.and hev).exists
          obtain ⟨hb0, hb1, x, y, ⟨hshape, hind, hcore, hxA, hyL, hyU⟩, ⟨-, hxnn, hybd⟩⟩ := hGam
          have hY := hys G b x y hcore hyL hyU
          obtain ⟨hxG, hy0, hbal, hout⟩ := hcore
          have hAeq : ∀ e, e ∉ q.arcs → x e = 0 := hxA
          have hmem : ∀ e, e ∈ q.arcs ↔ (∃ i, (i, q.pi i) = e) ∨ (∃ i, i ≠ q.s ∧ (i, q.pi (i-1)) = e) := by
            intro e; simp [Quadruple.arcs]
          have hpis1 : q.pi (q.s - 1) = q.s := by
            have := (q.successor_iff (q.s - 1)).2 rfl; rwa [sub_add_cancel] at this
          have F1 : outflow G x q.s = x (q.s, q.pi q.s) := by
            unfold outflow
            rw [Finset.sum_eq_single (q.s, q.pi q.s)]
            · intro e he hne
              rw [Finset.mem_filter] at he
              apply hAeq; rw [hmem]; rintro (⟨i, rfl⟩ | ⟨i, hi, rfl⟩)
              · simp only at he; obtain ⟨-, rfl⟩ := he; exact hne rfl
              · exact hi he.2
            · intro h; exfalso; apply h; rw [Finset.mem_filter]
              exact ⟨hsub ((hmem _).2 (Or.inl ⟨_, rfl⟩)), rfl⟩
          have F2 : inflow G x q.s = x (q.s - 1, q.s) := by
            unfold inflow
            rw [Finset.sum_eq_single (q.s - 1, q.s)]
            · intro e he hne
              rw [Finset.mem_filter] at he
              apply hAeq; rw [hmem]; rintro (⟨i, rfl⟩ | ⟨i, hi, rfl⟩)
              · have : i = q.s - 1 := q.pi.injective (he.2.trans hpis1.symm)
                subst this; exact hne (by rw [hpis1])
              · have : i - 1 = q.s - 1 := q.pi.injective (he.2.trans hpis1.symm)
                exact hi (sub_left_injective this)
            · intro h; exfalso; apply h; rw [Finset.mem_filter]
              refine ⟨hsub ((hmem _).2 (Or.inl ⟨q.s - 1, ?_⟩)), rfl⟩
              rw [hpis1]
          have F3 : x (q.s, q.pi q.s) ≤ inflow G x (q.pi q.s) := by
            unfold inflow
            apply Finset.single_le_sum (f := x) (fun e he => hxnn e (Finset.mem_filter.1 he).1)
            rw [Finset.mem_filter]; exact ⟨hsub ((hmem _).2 (Or.inl ⟨_, rfl⟩)), rfl⟩
          have F4 : x (q.s - 1, q.s) ≤ outflow G x (q.s - 1) := by
            unfold outflow
            apply Finset.single_le_sum (f := x) (fun e he => hxnn e (Finset.mem_filter.1 he).1)
            rw [Finset.mem_filter]
            refine ⟨hsub ((hmem _).2 (Or.inl ⟨q.s - 1, ?_⟩)), rfl⟩
            rw [hpis1]
          have hn1 : n - 1 = 2 * k := by omega
          rw [hn1] at hY hyU hybd hout
          have hnR : (n:ℝ) = 2 * k + 1 := by rw [hn]; push_cast; ring
          have hbn : b ^ n = b ^ (2*k+1) := by rw [hn]
          rw [hnR, hbn] at hY
          have hcase : ∀ i : Fin n, i ≠ q.s → i = 0 ∨ i ∈ q.L ∨ i ∈ q.U := by
            intro i hi
            by_cases h0 : i = 0
            · exact Or.inl h0
            · right
              have : i ∈ q.L ∪ q.U := by rw [q.partition]; simp [h0, hi]
              simpa using this
          have hsLU : q.s ∉ q.L ∧ q.s ∉ q.U := by
            have : q.s ∉ q.L ∪ q.U := by rw [q.partition]; simp
            simpa using this
          have hYbd := hybd q.s q.s_ne_root
          -- outflow and inflow values by class
          have houtL : ∀ i ∈ q.L, outflow G x i = b ^ (2*k) := by
            intro i hi
            have h0 : i ≠ 0 := fun h => by
              have : i ∈ q.L ∪ q.U := Finset.mem_union_left _ hi
              rw [q.partition] at this; simp [h] at this
            have := hout i; simp [h0, hyL i hi] at this; linarith
          have houtU : ∀ i ∈ q.U, outflow G x i = b := by
            intro i hi
            have h0 : i ≠ 0 := fun h => by
              have : i ∈ q.L ∪ q.U := Finset.mem_union_right _ hi
              rw [q.partition] at this; simp [h] at this
            have := hout i; simp [h0, hyU i hi] at this; linarith
          have hout0 : outflow G x 0 = 1 := by have := hout 0; simpa using this
          have houts : outflow G x q.s = b ^ (2*k) + y q.s := by
            have := hout q.s; simp [q.s_ne_root] at this; linarith
          have hinL : ∀ i ∈ q.L, b * inflow G x i = b ^ (2*k) := by
            intro i hi
            have h0 : i ≠ 0 := fun h => by
              have : i ∈ q.L ∪ q.U := Finset.mem_union_left _ hi
              rw [q.partition] at this; simp [h] at this
            have := hbal i; simp [h0] at this; linarith [houtL i hi]
          have hinU : ∀ i ∈ q.U, inflow G x i = 1 := by
            intro i hi
            have h0 : i ≠ 0 := fun h => by
              have : i ∈ q.L ∪ q.U := Finset.mem_union_right _ hi
              rw [q.partition] at this; simp [h] at this
            have := hbal i; simp [h0] at this
            have h2 : b * (inflow G x i - 1) = 0 := by linarith [houtU i hi]
            rcases mul_eq_zero.1 h2 with h | h
            · linarith
            · linarith
          have hin0 : inflow G x 0 = b ^ (2*k) := by
            have := hbal 0; simp at this
            have h2 : b * (inflow G x 0 - b ^ (2*k)) = 0 := by
              rw [hout0, hbn, pow_succ] at this; linear_combination -this
            rcases mul_eq_zero.1 h2 with h | h
            · linarith
            · linarith
          have hins : b * inflow G x q.s = b ^ (2*k) + y q.s := by
            have := hbal q.s; simp [q.s_ne_root] at this; linarith
          -- the key polynomial Δ
          have hgeom : (1 - b) * ∑ i ∈ Finset.range (2*k), b^(i+1) = b - b^(2*k+1) := by
            have := geom_sum_mul b (2*k)
            rw [Finset.sum_congr rfl (fun i _ => pow_succ b i), ← Finset.sum_mul, pow_succ]
            linear_combination (-b) * this
          have hΔ := hΔgen b hb0 hb1 hbδ
          set S := ∑ i ∈ Finset.range (2*k), b^(i+1) with hS
          have hY2 : 2 * k * b ^ (2*k) + q.U.card * (b - b ^ (2*k)) + y q.s = S := by
            have h : (1 - b) * (2 * k * b ^ (2*k) + q.U.card * (b - b ^ (2*k)) + y q.s - S) = 0 := by
              linear_combination hY - hgeom
            rcases mul_eq_zero.1 h with h | h
            · linarith
            · linarith
          have hkR : (2:ℝ) ≤ k := by exact_mod_cast hk2
          have hab : b * (1 - b) ≤ b - b ^ (2*k) := by
            have : b ^ (2*k) ≤ b ^ 2 := pow_le_pow_of_le_one hb0.le hb1.le (by omega)
            nlinarith
          have hbb : 0 < b * (1 - b) := mul_pos hb0 (by linarith)
          have hYeq : y q.s = ((k:ℝ) - q.U.card) * (b - b ^ (2*k)) -
              ((k:ℝ) * b + k * b ^ (2*k) - S) := by linear_combination hY2
          have hU : q.U.card = k - 1 := by
            have hUk : q.U.card ≤ 2 * k := by omega
            by_contra hne
            rcases (by omega : q.U.card ≤ k - 2 ∨ k ≤ q.U.card) with h | h
            · have h' : (q.U.card : ℝ) ≤ k - 2 := by
                have : ((q.U.card : ℕ) : ℝ) ≤ ((k - 2 : ℕ) : ℝ) := by exact_mod_cast h
                rw [Nat.cast_sub hk2] at this; simpa using this
              have : 2 * (b - b ^ (2*k)) ≤ ((k:ℝ) - q.U.card) * (b - b ^ (2*k)) :=
                mul_le_mul_of_nonneg_right (by linarith) (by linarith)
              linarith [hYbd.2, hΔ.2]
            · have h' : (k : ℝ) ≤ q.U.card := by exact_mod_cast h
              have : ((k:ℝ) - q.U.card) * (b - b ^ (2*k)) ≤ 0 :=
                mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
              linarith [hYbd.1, hΔ.1]
          have hL : q.L.card = k := by omega
          have hUR : (q.U.card : ℝ) = k - 1 := by rw [hU, Nat.cast_sub (by omega : 1 ≤ k)]; simp
          rw [hUR] at hYeq
          obtain ⟨D, hD⟩ : ∃ D : ℝ, D = (k:ℝ) * b + k * b ^ (2*k) - S := ⟨_, rfl⟩
          rw [← hD] at hYeq hΔ
          have hYv : y q.s = (b - b ^ (2*k)) - D := by linear_combination hYeq
          have hxs : x (q.s, q.pi q.s) = b ^ (2*k) + y q.s := by rw [← F1]; exact houts
          have hapos : 0 < b ^ (2*k) := by positivity
          refine ⟨⟨hU, hL⟩, ?_, ?_⟩
          · have hps : q.pi q.s ≠ q.s := q.fixedPointFree q.s
            rcases hcase _ hps with h | h | h
            · exfalso
              have h0' : inflow G x (q.pi q.s) = b ^ (2*k) := by rw [h]; exact hin0
              rw [hxs, h0'] at F3
              linarith [hYbd.1]
            · exfalso
              have hinl := hinL _ h
              rw [hxs] at F3
              have h1 := mul_le_mul_of_nonneg_left F3 hb0.le
              have h2 : b ^ (2*k) ≤ b ^ 3 := pow_le_pow_of_le_one hb0.le hb1.le (by omega)
              rw [hinl, hYv] at h1
              have h3 : b * (b * (1 - b) - D) ≤ 0 := by
                have e : b * (b * (1 - b) - D) = b * (b ^ (2*k) + (b - b ^ (2*k) - D)) - b ^ 3 := by ring
                rw [e]; linarith
              have h4 : 0 < b * (b * (1 - b) - D) := mul_pos hb0 (by linarith [hΔ.2])
              linarith
            · exact h
          · have hs1 : q.s - 1 ≠ q.s := by
              intro h; have := q.fixedPointFree (q.s - 1); rw [h] at this; exact this (by rw [← h, hpis1, h])
            rcases hcase _ hs1 with h | h | h
            · simp [R, h]
            · exfalso
              rw [houtL _ h, ← F2] at F4
              have h1 := mul_le_mul_of_nonneg_left F4 hb0.le
              rw [hins] at h1
              have h2 : b * b ^ (2*k) < b ^ (2*k) := mul_lt_of_lt_one_left hapos hb1
              linarith [hYbd.1]
            · exfalso
              rw [houtU _ h, ← F2] at F4
              have h1 := mul_le_mul_of_nonneg_left F4 hb0.le
              rw [hins, hYv] at h1
              have : b * (1 - b) ≤ D := by linarith
              linarith [hΔ.2]
        obtain ⟨G, hsub, hult⟩ := hfeas
        exact (hmp3 G hsub hult).2.2
      · obtain ⟨G, hsub, hult⟩ := hfeas
        have hult' : ∀ᶠ beta : ℝ in nhdsWithin (1:ℝ) (Set.Iio 1), q.basis ∈ Gam G beta := hult
        obtain ⟨b, hGam⟩ := hult'.exists
        obtain ⟨hb0, hb1, x, y, ⟨hshape, hind, hcore, hxA, hyL, hyU⟩, ⟨-, hxnn, hybd⟩⟩ := hGam
        obtain ⟨hxG, hy0, hbal, hout⟩ := hcore
        have hAeq : ∀ e, e ∉ q.arcs → x e = 0 := hxA
        have hmem : ∀ e, e ∈ q.arcs ↔ (∃ i, (i, q.pi i) = e) ∨ (∃ i, i ≠ q.s ∧ (i, q.pi (i-1)) = e) := by
          intro e; simp [Quadruple.arcs]
        have hpis1 : q.pi (q.s - 1) = q.s := by
          have := (q.successor_iff (q.s - 1)).2 rfl; rwa [sub_add_cancel] at this
        have F2 : inflow G x q.s = x (q.s - 1, q.s) := by
          unfold inflow
          rw [Finset.sum_eq_single (q.s - 1, q.s)]
          · intro e he hne
            rw [Finset.mem_filter] at he
            apply hAeq; rw [hmem]; rintro (⟨i, rfl⟩ | ⟨i, hi, rfl⟩)
            · have : i = q.s - 1 := q.pi.injective (he.2.trans hpis1.symm)
              subst this; exact hne (by rw [hpis1])
            · have : i - 1 = q.s - 1 := q.pi.injective (he.2.trans hpis1.symm)
              exact hi (sub_left_injective this)
          · intro h; exfalso; apply h; rw [Finset.mem_filter]
            refine ⟨hsub ((hmem _).2 (Or.inl ⟨q.s - 1, ?_⟩)), rfl⟩
            rw [hpis1]
        have F4 : x (q.s - 1, q.s) ≤ outflow G x (q.s - 1) := by
          unfold outflow
          apply Finset.single_le_sum (f := x) (fun e he => hxnn e (Finset.mem_filter.1 he).1)
          rw [Finset.mem_filter]
          refine ⟨hsub ((hmem _).2 (Or.inl ⟨q.s - 1, ?_⟩)), rfl⟩
          rw [hpis1]
        have hs1 : q.s - 1 ≠ q.s := by
          intro h; have := q.fixedPointFree (q.s - 1); rw [h] at this; exact this (by rw [← h, hpis1, h])
        have hYbd := hybd q.s q.s_ne_root
        have houts : outflow G x q.s = b ^ (n - 1) + y q.s := by
          have := hout q.s; simp [q.s_ne_root] at this; linarith
        have hins : b * inflow G x q.s = b ^ (n - 1) + y q.s := by
          have := hbal q.s; simp [q.s_ne_root] at this; linarith
        have hapos : 0 < b ^ (n - 1) := by positivity
        by_cases h0 : q.s - 1 = 0
        · simp [R, h0]
        have hLU : q.s - 1 ∈ q.L ∪ q.U := by rw [q.partition]; simp [h0, hs1]
        rcases Finset.mem_union.1 hLU with h | h
        · exfalso
          have houtL : outflow G x (q.s - 1) = b ^ (n - 1) := by
            have := hout (q.s - 1); simp [h0, hyL _ h] at this; linarith
          rw [houtL, ← F2] at F4
          have h1 := mul_le_mul_of_nonneg_left F4 hb0.le
          rw [hins] at h1
          have h2 : b * b ^ (n - 1) < b ^ (n - 1) := mul_lt_of_lt_one_left hapos hb1
          linarith [hYbd.1]
        · exact Finset.mem_union_right _ h
