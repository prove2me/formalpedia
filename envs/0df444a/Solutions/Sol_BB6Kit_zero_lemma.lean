-- Prove2me | solution 1 for BB6Kit.zero_lemma
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-24T06:24:25.248621+00:00
-- url     : https://prove2.me/submissions/41ce0d52-2470-4099-9234-ed2067720661
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit
import Theorems.Thm_BB6Kit_zero_rank

open Finset

namespace ZL

noncomputable def entR (c1 c2 c3 c4 α1 α2 α3 : ℕ) (p q : ℕ × ℕ × ℕ) : ℝ :=
  (Nat.choose (q.1 * c2 + q.2.2 * c1) p.1 : ℝ) * (Nat.choose (q.2.1 * c4 + q.2.2 * c3) p.2.1 : ℝ) *
    (α1 : ℝ) ^ (p.2.2 * q.1) * (α2 : ℝ) ^ (p.2.2 * q.2.1) * (α3 : ℝ) ^ (p.2.2 * q.2.2)

lemma tri_sum (q : ℕ) : ∑ v ∈ range q, ((q - v : ℕ) : ℝ) = (q:ℝ) * ((q:ℝ) + 1) / 2 := by
  induction q with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have h : ∑ v ∈ range n, ((n + 1 - v : ℕ) : ℝ) = ∑ v ∈ range n, (((n - v : ℕ) : ℝ) + 1) := by
      apply sum_congr rfl
      intro v hv
      rw [mem_range] at hv
      rw [show n + 1 - v = (n - v) + 1 by omega, Nat.cast_add, Nat.cast_one]
    rw [h, sum_add_distrib, ih, show n + 1 - n = 1 by omega]
    simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
    push_cast
    ring

lemma rowsum (K L : ℕ) (f : ℕ → ℝ) :
    ∑ p ∈ BB6Kit.rowSet K L, f p.2.2 = ((K:ℝ) * ((K:ℝ) + 1) / 2) * ∑ v ∈ range L, f v := by
  unfold BB6Kit.rowSet
  rw [sum_filter, sum_product]
  trans ∑ k ∈ range K, ((K - k : ℕ) : ℝ) * ∑ v ∈ range L, f v
  · apply sum_congr rfl
    intro k hk
    rw [mem_range] at hk
    rw [sum_product]
    try dsimp only
    have h2 : ∀ mm ∈ range K, ∑ v ∈ range L, (if k + mm ≤ K - 1 then f v else 0) =
        (if mm < K - k then (1:ℝ) else 0) * ∑ v ∈ range L, f v := by
      intro mm hmm
      rw [mem_range] at hmm
      by_cases hc : mm < K - k
      · rw [if_pos hc, one_mul]
        apply sum_congr rfl
        intro v _
        rw [if_pos (show k + mm ≤ K - 1 by omega)]
      · rw [if_neg hc, zero_mul]
        apply sum_eq_zero
        intro v _
        rw [if_neg (show ¬ (k + mm ≤ K - 1) by omega)]
    rw [sum_congr rfl h2, ← sum_mul, sum_boole]
    congr 1
    have hf2 : (range K).filter (fun mm => mm < K - k) = range (K - k) := by
      ext mm
      simp only [mem_filter, mem_range]
      constructor
      · intro h; exact h.2
      · intro h; exact ⟨by omega, h⟩
    rw [hf2, card_range]
  · rw [← sum_mul, tri_sum K]

end ZL

theorem solution (K L R S T N b1 b2 b3 α1 α2 α3 R1 S1 T1 R2 S2 T2 R3 S3 T3 : ℕ) (χ : ℝ)
    (hK : 3 ≤ K) (hL : 5 ≤ L) (hN : N = K * (K + 1) * L / 2) (hRST : N ≤ R * S * T)
    (hα1 : 1 < α1) (hα2 : 1 < α2) (hα3 : 1 < α3) (hind : BB6Kit.MultIndep α1 α2 α3)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3) (hgcd : Nat.gcd (Nat.gcd b1 b2) b3 = 1)
    (hΛ : ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) ≠ 0)
    (hpos : 0 < R1 ∧ 0 < S1 ∧ 0 < T1 ∧ 0 < R2 ∧ 0 < S2 ∧ 0 < T2 ∧ 0 < R3 ∧ 0 < S3 ∧ 0 < T3)
    (h27 : R1 + R2 + R3 < R ∧ S1 + S2 + S3 < S ∧ T1 + T2 + T3 < T) (hχ : 0 < χ)
    (h29 : (K : ℝ) * (max (max ((R1 : ℝ) + S1 + 1) ((S1 : ℝ) + T1 + 1)) (max ((R1 : ℝ) + T1 + 1) (χ * Real.sqrt (((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1))))) < (((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1)))
    (h210 : L < ((Finset.range (R1 + 1) ×ˢ Finset.range (S1 + 1) ×ˢ Finset.range (T1 + 1)).image (fun x => α1 ^ x.1 * α2 ^ x.2.1 * α3 ^ x.2.2)).card)
    (h211 : 2 * K * L < ((Finset.range (R2 + 1) ×ˢ Finset.range (S2 + 1) ×ˢ Finset.range (T2 + 1)).image (fun x => α1 ^ x.1 * α2 ^ x.2.1 * α3 ^ x.2.2)).card)
    (h212 : K ^ 2 < (R2 + 1) * (S2 + 1) * (T2 + 1))
    (h213 : 3 * K ^ 2 * L < (R3 + 1) * (S3 + 1) * (T3 + 1))
    (h214 : ¬ (b1 ≤ max R1 R2 ∧ b2 ≤ max S1 S2 ∧ b3 ≤ max T1 T2))
    (h215 : ¬ (∃ u1 u2 u3 : ℤ, u1 * (b1 : ℤ) + u2 * (b2 : ℤ) + u3 * (b3 : ℤ) = 0 ∧ Int.gcd (Int.gcd u1 u2 : ℤ) u3 = 1 ∧
        (|u1| : ℝ) ≤ ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1) / ((max (max ((R1 : ℝ) + S1 + 1) ((S1 : ℝ) + T1 + 1)) (max ((R1 : ℝ) + T1 + 1) (χ * Real.sqrt (((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1))))) - max (S1 : ℝ) T1) ∧
        (|u2| : ℝ) ≤ ((R1 : ℝ) + 1) * ((T1 : ℝ) + 1) / ((max (max ((R1 : ℝ) + S1 + 1) ((S1 : ℝ) + T1 + 1)) (max ((R1 : ℝ) + T1 + 1) (χ * Real.sqrt (((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1))))) - max (R1 : ℝ) T1) ∧
        (|u3| : ℝ) ≤ ((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) / ((max (max ((R1 : ℝ) + S1 + 1) ((S1 : ℝ) + T1 + 1)) (max ((R1 : ℝ) + T1 + 1) (χ * Real.sqrt (((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1))))) - max (R1 : ℝ) S1))) :
    ∃ kml rst : Fin N → ℕ × ℕ × ℕ, BB6Kit.RowsOK K L N kml ∧ BB6Kit.ColsOK R S T N rst ∧
      BB6Delta.deltaR N (b1 / Nat.gcd b1 b3) (b3 / Nat.gcd b1 b3) (b2 / Nat.gcd b2 b3) (b3 / Nat.gcd b2 b3) α1 α2 α3 kml rst ≠ 0 := by
  have hli := BB6Kit.zero_rank K L R S T N b1 b2 b3 α1 α2 α3 R1 S1 T1 R2 S2 T2 R3 S3 T3 χ hK hL hN hRST
    hα1 hα2 hα3 hind hb1 hb2 hb3 hgcd hΛ hpos h27 hχ h29 h210 h211 h212 h213 h214 h215
  generalize b1 / Nat.gcd b1 b3 = c1 at hli ⊢
  generalize b3 / Nat.gcd b1 b3 = c2 at hli ⊢
  generalize b2 / Nat.gcd b2 b3 = c3 at hli ⊢
  generalize b3 / Nat.gcd b2 b3 = c4 at hli ⊢
  -- the N × RST matrix, rows independent; C = its columns
  let A : Matrix (BB6Kit.rowSet K L) (range R ×ˢ range S ×ˢ range T) ℝ :=
    Matrix.of (fun p q => ZL.entR c1 c2 c3 c4 α1 α2 α3 p q)
  let C : (range R ×ˢ range S ×ˢ range T) → (BB6Kit.rowSet K L) → ℝ :=
    fun q p => ZL.entR c1 c2 c3 c4 α1 α2 α3 p q
  -- card of the row set is N
  have hKr : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hNA : (N:ℝ) = ((K:ℝ) * ((K:ℝ) + 1) / 2) * L := by
    have hdvd : 2 ∣ K * (K + 1) * L := (Nat.even_mul_succ_self K).two_dvd.mul_right L
    rw [hN, Nat.cast_div hdvd (by norm_num : ((2:ℕ):ℝ) ≠ 0)]
    push_cast
    ring
  have hcardR : ((BB6Kit.rowSet K L).card : ℝ) = N := by
    rw [hNA]
    have := ZL.rowsum K L (fun _ => (1:ℝ))
    simp only [sum_const, card_range, nsmul_eq_mul, mul_one] at this
    exact this
  have hc1 : Fintype.card (BB6Kit.rowSet K L) = N := by
    rw [Fintype.card_coe]; exact_mod_cast hcardR
  -- column rank = N, so the columns span everything
  have hrkA : A.rank = Fintype.card (BB6Kit.rowSet K L) := by
    rw [Matrix.rank_eq_finrank_span_row]
    exact finrank_span_eq_card hli
  have hrkT : A.transpose.rank = Module.finrank ℝ (Submodule.span ℝ (Set.range C)) := by
    rw [Matrix.rank_eq_finrank_span_row]
    rfl
  have hrk : Module.finrank ℝ (Submodule.span ℝ (Set.range C)) = Fintype.card (BB6Kit.rowSet K L) := by
    rw [← hrkT, Matrix.rank_transpose, hrkA]
  have htop : Submodule.span ℝ (Set.range C) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hrk, Module.finrank_fintype_fun_eq_card]
  -- extract a basis among the columns
  obtain ⟨κ, a, ha, hsp, hli2⟩ := exists_linearIndependent' (K := ℝ) C
  haveI : Finite κ := Finite.of_injective a ha
  haveI : Fintype κ := Fintype.ofFinite κ
  let bas := Module.Basis.mk hli2 (le_of_eq (by rw [hsp, htop]))
  have hc2 : Fintype.card κ = N := by
    rw [← Module.finrank_eq_card_basis bas, Module.finrank_fintype_fun_eq_card, hc1]
  let e1 : Fin N ≃ BB6Kit.rowSet K L := (Fintype.equivFinOfCardEq hc1).symm
  let e2 : Fin N ≃ κ := (Fintype.equivFinOfCardEq hc2).symm
  refine ⟨fun i => ((e1 i : BB6Kit.rowSet K L) : ℕ × ℕ × ℕ),
    fun j => ((a (e2 j) : range R ×ˢ range S ×ˢ range T) : ℕ × ℕ × ℕ), ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro i j h
    exact e1.injective (Subtype.ext h)
  · intro i
    exact (e1 i).2
  · intro i j h
    exact e2.injective (ha (Subtype.ext h))
  · intro j
    have := (a (e2 j)).2
    simp only [mem_product, mem_range] at this
    exact this
  · have hcols : LinearIndependent ℝ
        ((LinearEquiv.funCongrLeft ℝ ℝ e1).toLinearMap ∘ (C ∘ a) ∘ e2) :=
      (hli2.comp e2 e2.injective).map' _ (LinearEquiv.ker _)
    unfold BB6Delta.deltaR
    apply isUnit_iff_ne_zero.mp
    rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_cols_iff_isUnit]
    convert hcols using 1
    all_goals first | rfl | (funext j i; rfl)
