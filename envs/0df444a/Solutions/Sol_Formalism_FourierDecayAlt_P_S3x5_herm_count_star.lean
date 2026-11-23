-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.herm_count_star
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:03.545816+00:00
-- url     : https://prove2.me/submissions/ebc47958-c9f6-48d3-9421-510ca33ad33f

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_densityProduct_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_two_le_q
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_exists_trace_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_norm_surj
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_card_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_exists_B
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_card_fibre
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_nd_count
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_card_of_fibres
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_rank_conj_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_gram_fromCols
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_rank_left_block

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Matrix Formalism.FourierDecayAlt.S3
variable {K : Type} [Field K] [Fintype K] [StarRing K]
namespace Formalism.FourierDecayAlt.P.S3x5
theorem _root_.solution {q : ℕ} (hs : ∀ x : K, star x = x ^ q) (hc : Fintype.card K = q ^ 2)
    (hUO : ∀ (b : ℕ) (J : Matrix (Fin b) (Fin b) K), Jᴴ = J → IsUnit J.det →
      (Nat.card {g : Matrix (Fin b) (Fin b) K // gᴴ * J * g = J} : ℝ) =
        (q : ℝ) ^ (b ^ 2) * densP (-1) q 1 b)
    (hW : ∀ (n a : ℕ) (J : Matrix (Fin n) (Fin n) K) (X Y : Matrix (Fin n) (Fin a) K),
      Jᴴ = J → IsUnit J.det → X.rank = a → Y.rank = a → Xᴴ * J * X = Yᴴ * J * Y →
      ∃ g : Matrix (Fin n) (Fin n) K, gᴴ * J * g = J ∧ g * X = Y)
    (n a : ℕ) (J : Matrix (Fin n) (Fin n) K) (T : Matrix (Fin a) (Fin a) K)
    (hJ : Jᴴ = J) (hdJ : IsUnit J.det) (hT : Tᴴ = T) :
    (Nat.card {X : Matrix (Fin n) (Fin a) K // X.rank = a ∧ Xᴴ * J * X = T} : ℝ) =
      (q : ℝ) ^ ((2 * n * a : ℤ) - a ^ 2) *
        densP (-1) q ((n : ℤ) - a - ((a : ℤ) - T.rank) + 1) n := by
  classical
  have hq : 2 ≤ q := two_le_q hc
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hrk : T.rank ≤ a := by simpa using rank_le_card_width T
  rcases lt_or_ge n a with hlt | hle
  · rw [densityProduct_eq_zero _ _ _ _ (by omega) (by omega), mul_zero]
    have : IsEmpty {X : Matrix (Fin n) (Fin a) K // X.rank = a ∧ Xᴴ * J * X = T} := by
      constructor
      rintro ⟨X, hX, -⟩
      have h2 := rank_le_card_height X
      rw [Fintype.card_fin] at h2
      omega
    simp
  · obtain ⟨c, hcdef⟩ : ∃ c, c = a - T.rank := ⟨_, rfl⟩
    have hex := exists_B a T hT
    rw [← hcdef] at hex
    obtain ⟨B, hB⟩ := hex
    let P := {p : Matrix (Fin n) (Fin a) K × Matrix (Fin n) (Fin c) K //
      p.1.rank = a ∧ p.1ᴴ * J * p.1 = T ∧ p.1ᴴ * J * p.2 = B}

    let f1 : P → {X : Matrix (Fin n) (Fin a) K // X.rank = a ∧ Xᴴ * J * X = T} :=
      fun p => ⟨p.1.1, p.2.1, p.2.2.1⟩
    have c1 : (Nat.card P : ℝ) =
        Nat.card {X : Matrix (Fin n) (Fin a) K // X.rank = a ∧ Xᴴ * J * X = T} *
          (((Fintype.card K) ^ ((n - a) * c) : ℕ) : ℝ) := by
      apply card_of_fibres f1
      intro X
      congr 1
      rw [← card_fibre (X.1ᴴ * J) (rank_conj_mul X.1 X.2.1 J hdJ) B]
      apply Nat.card_congr
      refine ⟨fun p => ⟨p.1.1.2, ?_⟩, fun Y => ⟨⟨(X.1, Y.1), X.2.1, X.2.2, Y.2⟩, rfl⟩, ?_, ?_⟩
      · have h : p.1.1.1 = X.1 := congrArg Subtype.val p.2
        rw [← h]; exact p.1.2.2.2
      · intro p
        have h : p.1.1.1 = X.1 := congrArg Subtype.val p.2
        exact Subtype.ext (Subtype.ext (Prod.ext h.symm rfl))
      · intro Y; rfl

    have hherm : ∀ Y : Matrix (Fin n) (Fin c) K, (Yᴴ * J * Y)ᴴ = Yᴴ * J * Y := by
      intro Y
      rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ, Matrix.mul_assoc]
    let f2 : P → {D : Matrix (Fin c) (Fin c) K // Dᴴ = D} := fun p => ⟨p.1.2ᴴ * J * p.1.2, hherm _⟩
    have c2 : (Nat.card P : ℝ) = Nat.card {D : Matrix (Fin c) (Fin c) K // Dᴴ = D} *
        ((q : ℝ) ^ ((2 * n * (Fintype.card (Fin a ⊕ Fin c)) : ℤ) - (Fintype.card (Fin a ⊕ Fin c)) ^ 2) *
          densP (-1) q ((n : ℤ) - Fintype.card (Fin a ⊕ Fin c) + 1) n) := by
      apply card_of_fibres f2
      intro D
      have hS : (fromBlocks T B Bᴴ D.1)ᴴ = fromBlocks T B Bᴴ D.1 := by
        rw [fromBlocks_conjTranspose, hT, D.2, conjTranspose_conjTranspose]
      rw [← nd_count hq (exists_trace_ne hs hc) (norm_surj hs hc) hUO hW n J (fromBlocks T B Bᴴ D.1)
        hJ hdJ hS (hB D.1)]
      congr 1
      apply Nat.card_congr
      refine ⟨fun p => ⟨fromCols p.1.1.1 p.1.1.2, ?_⟩,
        fun Z => ⟨⟨(Z.1.toCols₁, Z.1.toCols₂), ?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
      · have h : p.1.1.2ᴴ * J * p.1.1.2 = D.1 := congrArg Subtype.val p.2
        rw [gram_fromCols, p.1.2.2.1, p.1.2.2.2, h]
        congr 1
        have h5 := congrArg conjTranspose p.1.2.2.2
        rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ,
          ← Matrix.mul_assoc] at h5
        exact h5
      · have h := Z.2
        rw [← fromCols_toCols Z.1] at h
        simpa using rank_left_block J _ _ _ (hB D.1) h
      · have h := Z.2
        rw [← fromCols_toCols Z.1, gram_fromCols, fromBlocks_inj] at h
        exact h.1
      · have h := Z.2
        rw [← fromCols_toCols Z.1, gram_fromCols, fromBlocks_inj] at h
        exact h.2.1
      · have h := Z.2
        rw [← fromCols_toCols Z.1, gram_fromCols, fromBlocks_inj] at h
        exact Subtype.ext h.2.2.2
      · intro p
        exact Subtype.ext (Subtype.ext (Prod.ext (toCols₁_fromCols _ _) (toCols₂_fromCols _ _)))
      · intro Z
        exact Subtype.ext (fromCols_toCols _)
    rw [card_herm hs hc c, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at c2
    rw [c1, hc] at c2
    have hcc : (c : ℤ) = (a : ℤ) - T.rank := by omega
    have hlo : (n : ℤ) - a - ((a : ℤ) - T.rank) + 1 = (n : ℤ) - ((a + c : ℕ) : ℤ) + 1 := by
      push_cast; omega
    rw [hlo]
    have hna : ((n - a : ℕ) : ℤ) = (n : ℤ) - a := by omega
    have hpw : (((q ^ (c ^ 2) : ℕ) : ℝ)) * (q : ℝ) ^ ((2 * n * ((a + c : ℕ) : ℤ) : ℤ) - ((a + c : ℕ) : ℤ) ^ 2) =
        (q : ℝ) ^ ((2 * n * a : ℤ) - a ^ 2) * ((((q ^ 2) ^ ((n - a) * c) : ℕ)) : ℝ) := by
      push_cast
      rw [← pow_mul, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hq0.ne', ← zpow_add₀ hq0.ne']
      congr 1
      push_cast [hna]
      ring
    have hpp : (0 : ℝ) < (((q ^ 2) ^ ((n - a) * c) : ℕ) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (by positivity)
    have : ((Nat.card {X : Matrix (Fin n) (Fin a) K // X.rank = a ∧ Xᴴ * J * X = T} : ℝ) -
        (q : ℝ) ^ ((2 * n * a : ℤ) - a ^ 2) * densP (-1) q ((n : ℤ) - ((a + c : ℕ) : ℤ) + 1) n) *
        (((q ^ 2) ^ ((n - a) * c) : ℕ) : ℝ) = 0 := by
      linear_combination c2 + densP (-1) q ((n : ℤ) - ((a + c : ℕ) : ℤ) + 1) n * hpw
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hpp.ne'
end Formalism.FourierDecayAlt.P.S3x5
