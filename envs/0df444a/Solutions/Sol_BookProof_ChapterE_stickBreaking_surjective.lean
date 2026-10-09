-- Prove2me | solution 1 for BookProof.ChapterE.stickBreaking_surjective
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:27:57.493778+00:00
-- url     : https://prove2.me/submissions/5fc2cf36-4045-4649-9056-14bb7d51db86

-- Generated from ChapterE.lean — solution of BookProof.ChapterE.stickBreaking_surjective
import Mathlib
import Definitions.Def_ChapterE
open BookProof.ChapterE



open scoped Matrix BigOperators
open Filter
open scoped Topology

set_option maxHeartbeats 1000000 in
theorem solution {N : ℕ} (P : Fin N → ℝ)
    (hP0 : ∀ n, 0 ≤ P n) (hPsum : ∑ n, P n = 1) :
    ∃ θ : Fin N → ℝ, ∀ n, stickBreaking θ n = P n := by

  induction N with
  | zero => ?_
  | succ N ih => ?_
  · aesop;
  · -- Define the tail T_n for n in Fin (N+1)
    let T : Fin (N + 1) → ℝ := fun n => ∑ k ∈ Finset.Ici n, P k;
    -- Prove that $T_n$ is nonincreasing, $T_0 = 1$, each $T_n \geq 0$, and $T_n = P_n + T_{n+1}$
    -- for the successor within range.
    have hT_noninc : ∀ n m : Fin (N + 1), n ≤ m → T m ≤ T n := by
      exact fun n m hnm =>
        Finset.sum_le_sum_of_subset_of_nonneg ( Finset.Ici_subset_Ici.mpr hnm ) fun _ _ _ => hP0 _
    have hT0 : T 0 = 1 := by
      convert hPsum using 1;
      exact Finset.sum_subset ( Finset.subset_univ _ ) fun x hx₁ hx₂ => by aesop;
    have hT_pos : ∀ n : Fin (N + 1), 0 ≤ T n := by
      exact fun n => Finset.sum_nonneg fun _ _ => hP0 _
    have hT_succ : ∀ n : Fin N, T (Fin.succ n) = T (Fin.castSucc n) - P (Fin.castSucc n) := by
      intro n; simp only [T] ; ring;
      rw [ eq_sub_iff_add_eq',
        ← Finset.sum_erase_add _ _
          ( show n.castSucc ∈ Finset.Ici n.castSucc from Finset.mem_Ici.mpr le_rfl ),
        add_comm ];
      rcongr k ; aesop;
    -- Choose angles: for each `n`, if `T n > 0` pick `θ n` with `Real.cos (θ n) ^ 2 = P n / T n`
    -- (possible by `cos_sq_surjective`, since `0 ≤ P n / T n ≤ 1` as `0 ≤ P n ≤ T n`); if `T n = 0`
    -- pick `θ n` with `Real.cos (θ n)^2 = 0` i.e. `θ n = π/2` so `Real.sin (θ n)^2 = 1`...
    obtain ⟨θ, hθ⟩ : ∃ θ : Fin (N + 1) → ℝ,
        ∀ n : Fin (N + 1), Real.cos (θ n) ^ 2 = if T n > 0 then P n / T n else 0 := by
      use fun n => Real.arccos ( Real.sqrt ( if T n > 0 then P n / T n else 0 ) );
      intro n; split_ifs <;> simp_all only [gt_iff_lt, ↓reduceIte, Real.sqrt_div, not_lt, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]  ;
      · rw [ Real.cos_arccos ];
        · rw [ div_pow, Real.sq_sqrt ( hP0 n ), Real.sq_sqrt ( hT_pos n ) ];
        · exact le_trans ( by norm_num )
            ( div_nonneg ( Real.sqrt_nonneg _ ) ( Real.sqrt_nonneg _ ) );
        · exact div_le_one_of_le₀
            ( Real.sqrt_le_sqrt <| Finset.single_le_sum ( fun a _ => hP0 a ) <|
              Finset.mem_Ici.mpr <| le_refl n ) <| Real.sqrt_nonneg _;
      · rw [ if_neg ( by linarith [ hT_pos n ] ) ] ; norm_num [ Real.cos_arccos ];
    -- Prove that $\prod_{k < n} \sin^2(\theta_k) = T_n$.
    have h_prod_sin_sq : ∀ n : Fin (N + 1), (∏ k ∈ Finset.Iio n, Real.sin (θ k) ^ 2) = T n := by
      intro n
      induction n using Fin.induction with
      | zero => ?_
      | succ n ih => ?_
      · aesop;
      · rw [ show ( Finset.Iio ( Fin.succ n ) : Finset ( Fin ( N + 1 ) ) ) =
            Finset.Iio ( Fin.castSucc n ) ∪ { Fin.castSucc n } from ?_,
          Finset.prod_union ] <;> norm_num [ ih, hT_succ ];
        · rw [ Real.sin_sq, hθ ];
          grind;
        · ext; simp only [Finset.mem_Iio, Finset.mem_Iic];
          exact ⟨ fun h => Nat.le_of_lt_succ h, fun h => Nat.lt_succ_of_le h ⟩;
    use θ; intro n; simp only [stickBreaking, h_prod_sin_sq, hθ, gt_iff_lt, mul_ite, mul_zero] ;
    split_ifs <;> simp_all only [gt_iff_lt, ne_eq, ne_of_gt, not_false_eq_true, mul_div_cancel₀,
        not_lt];
    exact Eq.symm ( le_antisymm
      ( le_trans ( Finset.single_le_sum ( fun a _ => hP0 a ) ( by aesop ) ) ‹T n ≤ 0› )
      ( hP0 n ) )
