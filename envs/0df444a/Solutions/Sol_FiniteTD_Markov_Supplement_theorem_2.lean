-- Prove2me | solution 1 for FiniteTD.Markov.Supplement.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:09:46.910153+00:00
-- url     : https://prove2.me/submissions/d90a33c4-de3e-49d7-96a8-555728860fc0

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting
import Definitions.Def_FiniteTD_Markov_Supplement_MeanPathIid

open FiniteTD
open FiniteTD.Markov
open FiniteTD.Markov.Supplement

theorem solution {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {d : ℕ} [NeZero d]
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (γ : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (ω : ℝ) (θstar θ0 : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hφ : ∀ s, ‖φ s‖ ≤ 1)
    (hω : IsMinEig π φ ω) (hω0 : 0 < ω)
    (hstar : gbar π P γ Rw φ θstar = 0) :
    -- (a) T ≥ (8/(1-γ))², constant step size 1/√T, averaged iterate
    (∀ T : ℕ, (8 / (1 - γ)) ^ 2 ≤ (T : ℝ) → ∀ α : ℕ → ℝ, (∀ t ≤ T, α t = 1 / Real.sqrt T) →
      iidExp π P T (fun o => dNormSq π φ (θstar - avgSeq (tdIid γ Rw φ α θ0 o) T)) ≤
        (‖θstar - θ0‖ ^ 2 + 2 * sigmaSq π P γ Rw φ θstar) / (Real.sqrt T * (1 - γ))) ∧
    -- (b) constant step size α₀ ≤ ω(1-γ)/8, last iterate
    (∀ α0 : ℝ, 0 ≤ α0 → α0 ≤ ω * (1 - γ) / 8 →
      ∀ T : ℕ, ∀ α : ℕ → ℝ, (∀ t ≤ T, α t = α0) →
      iidExp π P T (fun o => ‖θstar - tdIid γ Rw φ α θ0 o T‖ ^ 2) ≤
        Real.exp (-α0 * (1 - γ) * ω * T) * ‖θstar - θ0‖ ^ 2
          + α0 * (2 * sigmaSq π P γ Rw φ θstar / ((1 - γ) * ω))) ∧
    -- (c) decaying step size β/(λ + t), β = 2/((1-γ)ω), λ = 16/((1-γ)²ω), last iterate
    (∀ α : ℕ → ℝ,
      (∀ t : ℕ, α t = (2 / ((1 - γ) * ω)) / (16 / ((1 - γ) ^ 2 * ω) + t)) →
      ∀ T : ℕ,
      iidExp π P T (fun o => ‖θstar - tdIid γ Rw φ α θ0 o T‖ ^ 2) ≤
        max (8 * sigmaSq π P γ Rw φ θstar / ((1 - γ) ^ 2 * ω ^ 2))
            (16 * ‖θstar - θ0‖ ^ 2 / ((1 - γ) ^ 2 * ω))
          / (16 / ((1 - γ) ^ 2 * ω) + T)) := by
            obtain ⟨hP0, hP1⟩ := hP
            obtain ⟨hπ0, hπ1, hπP⟩ := hπ
            have hg : 0 < 1 - γ := by linarith
            have hp0 : ∀ s s', 0 ≤ π s * P s s' := fun s s' => mul_nonneg (hπ0 s) (hP0 s s')
            -- expectations of functions of s and s'
            have hE1 : ∀ f : S → ℝ, ∑ s, ∑ s', π s * P s s' * f s = ∑ s, π s * f s := by
              intro f
              refine Finset.sum_congr rfl fun s _ => ?_
              have : ∀ s', π s * P s s' * f s = (π s * f s) * P s s' := fun s' => by ring
              simp only [this]
              rw [← Finset.mul_sum, hP1, mul_one]
            have hE2 : ∀ f : S → ℝ, ∑ s, ∑ s', π s * P s s' * f s' = ∑ s, π s * f s := by
              intro f
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun s' _ => ?_
              rw [← Finset.sum_mul, hπP]
            have hEc : ∀ c : ℝ, ∑ s, ∑ s', π s * P s s' * c = c := by
              intro c
              rw [hE1 (fun _ => c), ← Finset.sum_mul, hπ1, one_mul]
            have hEmono : ∀ f g : S → S → ℝ, (∀ s s', f s s' ≤ g s s') →
                ∑ s, ∑ s', π s * P s s' * f s s' ≤ ∑ s, ∑ s', π s * P s s' * g s s' := by
              intro f g h
              exact Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun s' _ =>
                mul_le_mul_of_nonneg_left (h s s') (hp0 s s')
            have hEadd : ∀ f g : S → S → ℝ,
                ∑ s, ∑ s', π s * P s s' * (f s s' + g s s') =
                  ∑ s, ∑ s', π s * P s s' * f s s' + ∑ s, ∑ s', π s * P s s' * g s s' := by
              intro f g
              simp only [mul_add, Finset.sum_add_distrib]
            have hEsmul : ∀ (c : ℝ) (f : S → S → ℝ),
                ∑ s, ∑ s', π s * P s s' * (c * f s s') = c * ∑ s, ∑ s', π s * P s s' * f s s' := by
              intro c f
              simp only [Finset.mul_sum]
              refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => by ring
            -- inner product with gbar
            have hinner : ∀ u θ : EuclideanSpace ℝ (Fin d), inner ℝ u (gbar π P γ Rw φ θ)
                = ∑ s, ∑ s', π s * P s s' * inner ℝ u (tdDir γ Rw φ θ s s') := by
              intro u θ
              unfold gbar
              simp only [inner_sum, inner_smul_right]
            -- difference of directions
            have hdiff : ∀ θ s s', tdDir γ Rw φ θ s s' = tdDir γ Rw φ θstar s s' +
                (inner ℝ (φ s) (θstar - θ) - γ * inner ℝ (φ s') (θstar - θ)) • φ s := by
              intro θ s s'
              unfold tdDir
              rw [← add_smul]
              congr 1
              simp only [inner_sub_right]
              ring
            set σ2 := sigmaSq π P γ Rw φ θstar with hσ2
            have hσ0 : 0 ≤ σ2 := by
              rw [hσ2]; unfold sigmaSq tupleExp
              exact Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun s' _ =>
                mul_nonneg (hp0 s s') (sq_nonneg _)
            have hD0 : ∀ u, 0 ≤ dNormSq π φ u := by
              intro u
              unfold dNormSq
              exact Finset.sum_nonneg fun s _ => mul_nonneg (hπ0 s) (sq_nonneg _)
            -- Lemma 3
            have hL3 : ∀ θ, (1 - γ) * dNormSq π φ (θstar - θ) ≤
                inner ℝ (θstar - θ) (gbar π P γ Rw φ θ) := by
              intro θ
              have h0 : ∑ s, ∑ s', π s * P s s' * inner ℝ (θstar - θ) (tdDir γ Rw φ θstar s s') = 0 := by
                rw [← hinner, hstar, inner_zero_right]
              have h1 : ∀ s s', inner ℝ (θstar - θ) (tdDir γ Rw φ θ s s') =
                  inner ℝ (θstar - θ) (tdDir γ Rw φ θstar s s') +
                  (inner ℝ (φ s) (θstar - θ) - γ * inner ℝ (φ s') (θstar - θ)) * inner ℝ (φ s) (θstar - θ) := by
                intro s s'
                rw [hdiff θ s s', inner_add_right, inner_smul_right, real_inner_comm (φ s)]
              rw [hinner]
              simp only [h1]
              rw [hEadd, h0, zero_add]
              have h2 : ∑ s, ∑ s', π s * P s s' * ((1 - γ / 2) * (inner ℝ (φ s) (θstar - θ)) ^ 2
                  + (-(γ / 2)) * (inner ℝ (φ s') (θstar - θ)) ^ 2) = (1 - γ) * dNormSq π φ (θstar - θ) := by
                rw [hEadd (fun s s' => (1 - γ / 2) * (inner ℝ (φ s) (θstar - θ)) ^ 2)
                  (fun s s' => (-(γ / 2)) * (inner ℝ (φ s') (θstar - θ)) ^ 2)]
                rw [hEsmul _ (fun s s' => (inner ℝ (φ s) (θstar - θ)) ^ 2),
                  hEsmul _ (fun s s' => (inner ℝ (φ s') (θstar - θ)) ^ 2),
                  hE1 (fun s => (inner ℝ (φ s) (θstar - θ)) ^ 2),
                  hE2 (fun s => (inner ℝ (φ s) (θstar - θ)) ^ 2)]
                unfold dNormSq
                ring
              rw [← h2]
              apply hEmono
              intro s s'
              linear_combination (1/2) * mul_nonneg hγ0 (sq_nonneg (inner ℝ (φ s) (θstar - θ) - inner ℝ (φ s') (θstar - θ)))
            -- Lemma 5
            have hL5 : ∀ θ, ∑ s, ∑ s', π s * P s s' * ‖tdDir γ Rw φ θ s s'‖ ^ 2 ≤
                2 * σ2 + 8 * dNormSq π φ (θstar - θ) := by
              intro θ
              have h2 : ∑ s, ∑ s', π s * P s s' * (2 * ‖tdDir γ Rw φ θstar s s'‖ ^ 2 +
                  (4 * (inner ℝ (φ s) (θstar - θ)) ^ 2
                  + 4 * (inner ℝ (φ s') (θstar - θ)) ^ 2)) = 2 * σ2 + 8 * dNormSq π φ (θstar - θ) := by
                rw [hEadd (fun s s' => 2 * ‖tdDir γ Rw φ θstar s s'‖ ^ 2)
                  (fun s s' => 4 * (inner ℝ (φ s) (θstar - θ)) ^ 2 + 4 * (inner ℝ (φ s') (θstar - θ)) ^ 2)]
                rw [hEadd (fun s s' => 4 * (inner ℝ (φ s) (θstar - θ)) ^ 2)
                  (fun s s' => 4 * (inner ℝ (φ s') (θstar - θ)) ^ 2)]
                rw [hEsmul _ (fun s s' => (inner ℝ (φ s) (θstar - θ)) ^ 2),
                  hEsmul _ (fun s s' => (inner ℝ (φ s') (θstar - θ)) ^ 2),
                  hEsmul _ (fun s s' => ‖tdDir γ Rw φ θstar s s'‖ ^ 2),
                  hE1 (fun s => (inner ℝ (φ s) (θstar - θ)) ^ 2),
                  hE2 (fun s => (inner ℝ (φ s) (θstar - θ)) ^ 2)]
                rw [hσ2]
                unfold dNormSq sigmaSq tupleExp
                ring
              rw [← h2]
              apply hEmono
              intro s s'
              rw [hdiff θ s s']
              generalize inner ℝ (φ s) (θstar - θ) = x
              generalize inner ℝ (φ s') (θstar - θ) = y
              generalize tdDir γ Rw φ θstar s s' = a
              have hb : ‖(x - γ * y) • φ s‖ ^ 2 ≤ (x - γ * y) ^ 2 := by
                rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
                have : ‖φ s‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (hφ s)
                exact mul_le_of_le_one_right (sq_nonneg _) this
              have hab : ‖a + (x - γ * y) • φ s‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖(x - γ * y) • φ s‖ ^ 2 := by
                have h1 := norm_add_le a ((x - γ * y) • φ s)
                have h2 : ‖a + (x - γ * y) • φ s‖ ^ 2 ≤ (‖a‖ + ‖(x - γ * y) • φ s‖) ^ 2 :=
                  pow_le_pow_left₀ (norm_nonneg _) h1 2
                linear_combination h2 + sq_nonneg (‖a‖ - ‖(x - γ * y) • φ s‖)
              have hy : γ ^ 2 * y ^ 2 ≤ y ^ 2 := by
                have : γ ^ 2 ≤ 1 := pow_le_one₀ hγ0 hγ1.le
                exact mul_le_of_le_one_left (sq_nonneg y) this
              linear_combination hab + 2 * hb + 4 * hy + 2 * sq_nonneg (x + γ * y)
            -- one step
            have hstep : ∀ (a : ℝ) (θ), 0 ≤ a → a ≤ (1 - γ) / 8 →
                ∑ s, ∑ s', π s * P s s' * ‖θstar - (θ + a • tdDir γ Rw φ θ s s')‖ ^ 2 ≤
                  ‖θstar - θ‖ ^ 2 - a * (1 - γ) * dNormSq π φ (θstar - θ) + 2 * a ^ 2 * σ2 := by
              intro a θ ha0 ha1
              have h1 : ∀ s s', ‖θstar - (θ + a • tdDir γ Rw φ θ s s')‖ ^ 2 =
                  ‖θstar - θ‖ ^ 2 + ((-2 * a) * inner ℝ (θstar - θ) (tdDir γ Rw φ θ s s')
                    + a ^ 2 * ‖tdDir γ Rw φ θ s s'‖ ^ 2) := by
                intro s s'
                rw [← sub_sub, norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
                  sq_abs]
                ring
              simp only [h1]
              rw [hEadd (fun s s' => ‖θstar - θ‖ ^ 2), hEc,
                hEadd (fun s s' => (-2 * a) * inner ℝ (θstar - θ) (tdDir γ Rw φ θ s s'))
                  (fun s s' => a ^ 2 * ‖tdDir γ Rw φ θ s s'‖ ^ 2),
                hEsmul _ (fun s s' => inner ℝ (θstar - θ) (tdDir γ Rw φ θ s s')),
                hEsmul _ (fun s s' => ‖tdDir γ Rw φ θ s s'‖ ^ 2), ← hinner]
              have h3 := mul_le_mul_of_nonneg_left (hL3 θ) ha0
              have h5 := mul_le_mul_of_nonneg_left (hL5 θ) (sq_nonneg a)
              have h6 : a * (a * dNormSq π φ (θstar - θ)) ≤ (1 - γ) / 8 * (a * dNormSq π φ (θstar - θ)) :=
                mul_le_mul_of_nonneg_right ha1 (mul_nonneg ha0 (hD0 _))
              linear_combination 2 * h3 + h5 + 8 * h6
            -- snoc decomposition
            have hprob0 : ∀ (n : ℕ) (o : Fin n → S × S), 0 ≤ iidProb π P n o := by
              intro n o
              unfold iidProb
              exact Finset.prod_nonneg fun i _ => hp0 _ _
            have hsnoc : ∀ (n : ℕ) (F : (Fin (n + 1) → S × S) → ℝ), iidExp π P (n + 1) F =
                iidExp π P n (fun o => ∑ s, ∑ s', π s * P s s' *
                  F (Fin.snoc (α := fun _ => S × S) o (s, s'))) := by
              intro n F
              unfold iidExp
              rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => S × S)).sum_comp, Fintype.sum_prod_type,
                Finset.sum_comm]
              refine Finset.sum_congr rfl fun o _ => ?_
              rw [Fintype.sum_prod_type, Finset.mul_sum]
              refine Finset.sum_congr rfl fun s _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun s' _ => ?_
              have : iidProb π P (n + 1) (Fin.snoc (α := fun _ => S × S) o (s, s')) =
                  iidProb π P n o * (π s * P s s') := by
                unfold iidProb
                rw [Fin.prod_univ_castSucc]
                simp
              simp only [Fin.snocEquiv, Equiv.coe_fn_mk]
              rw [this]
              ring
            have hmono : ∀ (n : ℕ) (F G : (Fin n → S × S) → ℝ), (∀ o, F o ≤ G o) →
                iidExp π P n F ≤ iidExp π P n G := by
              intro n F G h
              unfold iidExp
              exact Finset.sum_le_sum fun o _ => mul_le_mul_of_nonneg_left (h o) (hprob0 n o)
            have hIadd : ∀ (n : ℕ) (F G : (Fin n → S × S) → ℝ),
                iidExp π P n (fun o => F o + G o) = iidExp π P n F + iidExp π P n G := by
              intro n F G
              unfold iidExp
              simp only [mul_add, Finset.sum_add_distrib]
            have hIsmul : ∀ (n : ℕ) (c : ℝ) (F : (Fin n → S × S) → ℝ),
                iidExp π P n (fun o => c * F o) = c * iidExp π P n F := by
              intro n c F
              unfold iidExp
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun o _ => by ring
            have hIzero : ∀ (F : (Fin 0 → S × S) → ℝ), iidExp π P 0 F = F Fin.elim0 := by
              intro F
              unfold iidExp iidProb
              rw [Fintype.sum_unique]
              simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
              congr 1
            have hIconst : ∀ (n : ℕ) (c : ℝ), iidExp π P n (fun _ => c) = c := by
              intro n c
              induction n with
              | zero => rw [hIzero]
              | succ n ih => rw [hsnoc]; simp only [hEc]; exact ih
            -- iterates under snoc
            have htd : ∀ (α : ℕ → ℝ) (n : ℕ) (o : Fin n → S × S) (z : S × S) (t : ℕ), t ≤ n →
                tdIid γ Rw φ α θ0 (Fin.snoc (α := fun _ => S × S) o z) t = tdIid γ Rw φ α θ0 o t := by
              intro α n o z t
              induction t with
              | zero => intro _; simp [tdIid]
              | succ t ih =>
                intro ht
                have ht1 : t < n := ht
                have ht2 : t < n + 1 := by omega
                have hz : (Fin.snoc (α := fun _ => S × S) o z : Fin (n + 1) → S × S) ⟨t, ht2⟩ = o ⟨t, ht1⟩ := by
                  have : (⟨t, ht2⟩ : Fin (n + 1)) = Fin.castSucc ⟨t, ht1⟩ := rfl
                  rw [this, Fin.snoc_castSucc]
                simp only [tdIid, dif_pos ht1, dif_pos ht2, hz, ih ht1.le]
            have htdlast : ∀ (α : ℕ → ℝ) (n : ℕ) (o : Fin n → S × S) (z : S × S),
                tdIid γ Rw φ α θ0 (Fin.snoc (α := fun _ => S × S) o z) (n + 1) =
                  tdIid γ Rw φ α θ0 o n + α n • tdDir γ Rw φ (tdIid γ Rw φ α θ0 o n) z.1 z.2 := by
              intro α n o z
              have hz : (Fin.snoc (α := fun _ => S × S) o z : Fin (n + 1) → S × S) ⟨n, n.lt_succ_self⟩ = z := by
                have : (⟨n, n.lt_succ_self⟩ : Fin (n + 1)) = Fin.last n := rfl
                rw [this, Fin.snoc_last]
              simp only [tdIid, dif_pos n.lt_succ_self, hz, htd α n o z n le_rfl]
            -- D ≥ ω
            have hDω : ∀ u, ω * ‖u‖ ^ 2 ≤ dNormSq π φ u := by
              intro u
              by_cases hu : u = 0
              · subst hu; simpa using hD0 0
              · have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
                have h1 : ω ≤ dNormSq π φ ((‖u‖)⁻¹ • u) := by
                  refine hω.2 ⟨_, ?_, rfl⟩
                  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
                have h2 : dNormSq π φ u = ‖u‖ ^ 2 * dNormSq π φ ((‖u‖)⁻¹ • u) := by
                  unfold dNormSq
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun s _ => ?_
                  rw [inner_smul_right]
                  field_simp
                rw [h2, mul_comm]
                exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
            have hω1 : ω ≤ 1 := by
              obtain ⟨⟨u, hu, hu2⟩, _⟩ := hω
              rw [hu2, ← hπ1]
              unfold dNormSq
              refine Finset.sum_le_sum fun s _ => ?_
              have h1 : |inner ℝ (φ s) u| ≤ 1 := by
                have h2 := abs_real_inner_le_norm (φ s) u
                rw [hu, mul_one] at h2
                exact h2.trans (hφ s)
              have h3 : (inner ℝ (φ s) u) ^ 2 ≤ (1 : ℝ) := by
                rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) h1
              exact mul_le_of_le_one_right (hπ0 s) h3
            -- generic recursion for the last iterate
            have hrec : ∀ (α : ℕ → ℝ) (n : ℕ), 0 ≤ α n → α n ≤ (1 - γ) / 8 →
                iidExp π P (n + 1) (fun o => ‖θstar - tdIid γ Rw φ α θ0 o (n + 1)‖ ^ 2) ≤
                  (1 - α n * (1 - γ) * ω) * iidExp π P n (fun o => ‖θstar - tdIid γ Rw φ α θ0 o n‖ ^ 2)
                    + 2 * α n ^ 2 * σ2 := by
              intro α n h0 h1
              rw [hsnoc]
              simp only [htdlast]
              refine (hmono n _ (fun o => (1 - α n * (1 - γ) * ω) * ‖θstar - tdIid γ Rw φ α θ0 o n‖ ^ 2
                + 2 * α n ^ 2 * σ2) ?_).trans ?_
              · intro o
                refine (hstep (α n) (tdIid γ Rw φ α θ0 o n) h0 h1).trans ?_
                have := mul_le_mul_of_nonneg_left (hDω (θstar - tdIid γ Rw φ α θ0 o n)) (mul_nonneg h0 hg.le)
                linear_combination this
              · rw [hIadd n (fun o => (1 - α n * (1 - γ) * ω) * ‖θstar - tdIid γ Rw φ α θ0 o n‖ ^ 2),
                  hIsmul, hIconst]
            refine ⟨?_, ?_, ?_⟩
            · intro T hT α hα
              have hTpos : (0 : ℝ) < T := lt_of_lt_of_le (by positivity) hT
              have hsq : 0 < Real.sqrt T := Real.sqrt_pos.mpr hTpos
              have hsq8 : 8 / (1 - γ) ≤ Real.sqrt T := Real.le_sqrt_of_sq_le hT
              have hss : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hTpos.le
              set a := 1 / Real.sqrt T with ha
              have ha0 : 0 ≤ a := by positivity
              have ha1 : a ≤ (1 - γ) / 8 := by
                rw [ha, div_le_div_iff₀ hsq (by norm_num)]
                rw [div_le_iff₀ hg] at hsq8
                linarith
              have hind : ∀ n : ℕ, n ≤ T →
                  iidExp π P n (fun o => ‖θstar - tdIid γ Rw φ α θ0 o n‖ ^ 2 +
                    a * (1 - γ) * ∑ t ∈ Finset.range n, dNormSq π φ (θstar - tdIid γ Rw φ α θ0 o t)) ≤
                  ‖θstar - θ0‖ ^ 2 + n * (2 * a ^ 2 * σ2) := by
                intro n
                induction n with
                | zero => intro _; rw [hIzero]; simp [tdIid]
                | succ n ih =>
                  intro hn
                  have ih' := ih (by omega)
                  rw [hsnoc]
                  have hle : iidExp π P n (fun o => ∑ s, ∑ s', π s * P s s' *
                      (‖θstar - tdIid γ Rw φ α θ0 (Fin.snoc (α := fun _ => S × S) o (s, s')) (n + 1)‖ ^ 2 +
                        a * (1 - γ) * ∑ t ∈ Finset.range (n + 1), dNormSq π φ
                          (θstar - tdIid γ Rw φ α θ0 (Fin.snoc (α := fun _ => S × S) o (s, s')) t))) ≤
                      iidExp π P n (fun o => (‖θstar - tdIid γ Rw φ α θ0 o n‖ ^ 2 +
                    a * (1 - γ) * ∑ t ∈ Finset.range n, dNormSq π φ (θstar - tdIid γ Rw φ α θ0 o t))
                      + 2 * a ^ 2 * σ2) := by
                    apply hmono
                    intro o
                    have hs : ∀ s s', ∑ t ∈ Finset.range (n + 1), dNormSq π φ
                          (θstar - tdIid γ Rw φ α θ0 (Fin.snoc (α := fun _ => S × S) o (s, s')) t) =
                        ∑ t ∈ Finset.range (n + 1), dNormSq π φ (θstar - tdIid γ Rw φ α θ0 o t) := by
                      intro s s'
                      refine Finset.sum_congr rfl fun t ht => ?_
                      rw [htd α n o (s, s') t (by have := Finset.mem_range.mp ht; omega)]
                    simp only [hs, htdlast, hα n (by omega)]
                    rw [hEadd, hEc, Finset.sum_range_succ]
                    have := hstep a (tdIid γ Rw φ α θ0 o n) ha0 ha1
                    linear_combination this
                  refine hle.trans ?_
                  rw [hIadd n (fun o => ‖θstar - tdIid γ Rw φ α θ0 o n‖ ^ 2 +
                    a * (1 - γ) * ∑ t ∈ Finset.range n, dNormSq π φ (θstar - tdIid γ Rw φ α θ0 o t)), hIconst]
                  push_cast
                  linarith
              have hT1 := hind T le_rfl
              have hJ : ∀ o : Fin T → S × S, dNormSq π φ (θstar - avgSeq (tdIid γ Rw φ α θ0 o) T) ≤
                  (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, dNormSq π φ (θstar - tdIid γ Rw φ α θ0 o t) := by
                intro o
                unfold dNormSq
                rw [Finset.sum_comm, Finset.mul_sum]
                refine Finset.sum_le_sum fun s _ => ?_
                rw [← Finset.mul_sum, mul_left_comm]
                refine mul_le_mul_of_nonneg_left ?_ (hπ0 s)
                have h1 : inner ℝ (φ s) (θstar - avgSeq (tdIid γ Rw φ α θ0 o) T) =
                    (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, inner ℝ (φ s) (θstar - tdIid γ Rw φ α θ0 o t) := by
                  unfold avgSeq
                  simp only [inner_sub_right, inner_smul_right, inner_sum, Finset.sum_sub_distrib,
                    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
                  field_simp
                rw [h1]
                have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.range T)
                  (f := fun t => (inner ℝ (φ s) (θstar - tdIid γ Rw φ α θ0 o t) : ℝ))
                rw [Finset.card_range] at h2
                rw [mul_pow]
                calc _ ≤ ((T : ℝ)⁻¹) ^ 2 * (T * ∑ t ∈ Finset.range T,
                      (inner ℝ (φ s) (θstar - tdIid γ Rw φ α θ0 o t) : ℝ) ^ 2) :=
                      mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
                  _ = _ := by field_simp
              refine (hmono T _ _ hJ).trans ?_
              rw [hIsmul]
              rw [hIadd T (fun o => ‖θstar - tdIid γ Rw φ α θ0 o T‖ ^ 2), hIsmul] at hT1
              have hnn : 0 ≤ iidExp π P T (fun o => ‖θstar - tdIid γ Rw φ α θ0 o T‖ ^ 2) := by
                have := hmono T (fun _ => 0) (fun o => ‖θstar - tdIid γ Rw φ α θ0 o T‖ ^ 2)
                  (fun o => sq_nonneg _)
                rwa [hIconst] at this
              set X := iidExp π P T (fun o => ∑ t ∈ Finset.range T,
                dNormSq π φ (θstar - tdIid γ Rw φ α θ0 o t)) with hX
              have ha2 : (T : ℝ) * (2 * a ^ 2 * σ2) = 2 * σ2 := by
                have : (T : ℝ) * a ^ 2 = 1 := by
                  rw [ha, div_pow, one_pow, Real.sq_sqrt hTpos.le]; field_simp
                linear_combination 2 * σ2 * this
              rw [ha2] at hT1
              have h3 : a * (1 - γ) * X ≤ ‖θstar - θ0‖ ^ 2 + 2 * σ2 := by linarith
              rw [le_div_iff₀ (mul_pos hsq hg)]
              have h4 : (T : ℝ)⁻¹ * X * (Real.sqrt T * (1 - γ)) = a * (1 - γ) * X := by
                have : (T : ℝ)⁻¹ * Real.sqrt T = a := by
                  rw [ha]; nth_rewrite 1 [← hss]; field_simp
                rw [← this]; ring
              rw [h4]; exact h3
            · intro a ha0 ha1 T α hα
              have ha2 : a ≤ (1 - γ) / 8 := by
                have := mul_le_mul_of_nonneg_right hω1 hg.le
                linarith
              have hκ : a * (1 - γ) * ω ≤ 1 := by
                have h1 : a * (1 - γ) ≤ 1 := mul_le_one₀ (by linarith) hg.le (by linarith)
                exact mul_le_one₀ h1 hω0.le hω1
              have hC0 : 0 ≤ a * (2 * σ2 / ((1 - γ) * ω)) := by positivity
              have hκC : a * (1 - γ) * ω * (a * (2 * σ2 / ((1 - γ) * ω))) = 2 * a ^ 2 * σ2 := by
                field_simp
              have hind : ∀ n : ℕ, n ≤ T →
                  iidExp π P n (fun o => ‖θstar - tdIid γ Rw φ α θ0 o n‖ ^ 2) ≤
                  Real.exp (-a * (1 - γ) * ω * n) * ‖θstar - θ0‖ ^ 2
                    + a * (2 * σ2 / ((1 - γ) * ω)) := by
                intro n
                induction n with
                | zero =>
                  intro _; rw [hIzero]
                  simp only [tdIid, Nat.cast_zero, mul_zero, Real.exp_zero, one_mul]
                  linarith
                | succ n ih =>
                  intro hn
                  have ih' := ih (by omega)
                  have hαn : α n = a := hα n (by omega)
                  have hr := hrec α n (by rw [hαn]; exact ha0) (by rw [hαn]; exact ha2)
                  rw [hαn] at hr
                  refine hr.trans ?_
                  have hexp : Real.exp (-a * (1 - γ) * ω * ((n + 1 : ℕ) : ℝ)) =
                      Real.exp (-(a * (1 - γ) * ω)) * Real.exp (-a * (1 - γ) * ω * n) := by
                    rw [← Real.exp_add]; congr 1; push_cast; ring
                  have he : 1 - a * (1 - γ) * ω ≤ Real.exp (-(a * (1 - γ) * ω)) := by
                    have := Real.add_one_le_exp (-(a * (1 - γ) * ω)); linarith
                  have h1 := mul_le_mul_of_nonneg_left ih' (sub_nonneg.mpr hκ)
                  have h2 := mul_le_mul_of_nonneg_right he (mul_nonneg
                    (Real.exp_pos (-a * (1 - γ) * ω * n)).le (sq_nonneg ‖θstar - θ0‖))
                  rw [hexp]
                  linear_combination h1 + h2 - hκC
              exact hind T le_rfl
            · intro α hα T
              set lam := 16 / ((1 - γ) ^ 2 * ω) with hlam
              have hlam16 : 16 ≤ lam := by
                rw [hlam, le_div_iff₀ (by positivity)]
                have : (1 - γ) ^ 2 ≤ 1 := pow_le_one₀ hg.le (by linarith)
                have h' := mul_le_one₀ this hω0.le hω1
                linarith
              set ν := max (8 * σ2 / ((1 - γ) ^ 2 * ω ^ 2))
                      (16 * ‖θstar - θ0‖ ^ 2 / ((1 - γ) ^ 2 * ω)) with hν
              have hν1 : 8 * σ2 / ((1 - γ) ^ 2 * ω ^ 2) ≤ ν := le_max_left _ _
              have hν2 : 16 * ‖θstar - θ0‖ ^ 2 / ((1 - γ) ^ 2 * ω) ≤ ν := le_max_right _ _
              have hν0 : 0 ≤ ν := le_trans (by positivity) hν1
              induction T with
              | zero =>
                rw [hIzero]
                simp only [tdIid, Nat.cast_zero, add_zero]
                rw [le_div_iff₀ (by linarith)]
                refine le_trans (le_of_eq ?_) hν2
                rw [hlam]; ring
              | succ n ih =>
                have hx : 16 ≤ lam + n := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
                have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
                have hβ : 0 < 2 / ((1 - γ) * ω) := by positivity
                have h0 : 0 ≤ α n := by rw [hα]; exact div_nonneg hβ.le (by linarith)
                have h1 : α n ≤ (1 - γ) / 8 := by
                  rw [hα, div_le_iff₀ (by linarith)]
                  have : 2 / ((1 - γ) * ω) = (1 - γ) / 8 * lam := by
                    rw [hlam]; field_simp; try norm_num
                  rw [this]
                  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
                have hr := hrec α n h0 h1
                refine hr.trans ?_
                push_cast
                rw [← add_assoc]
                have hk : α n * (1 - γ) * ω = 2 / (lam + n) := by
                  rw [hα]; field_simp
                have hk2 : 2 * α n ^ 2 * σ2 = 8 * σ2 / ((1 - γ) ^ 2 * ω ^ 2) / (lam + n) ^ 2 := by
                  rw [hα]; field_simp; try ring
                rw [hk, hk2]
                generalize hxx : lam + (n : ℝ) = x at *
                have hx0 : 0 < x := by linarith
                have h3 : 0 ≤ 1 - 2 / x := by
                  rw [sub_nonneg, div_le_one hx0]; linarith
                have h4 := mul_le_mul_of_nonneg_left ih h3
                have h5 := div_le_div_of_nonneg_right hν1 (sq_nonneg x)
                have h6 : (1 - 2 / x) * (ν / x) + ν / x ^ 2 ≤ ν / (x + 1) := by
                  have : (1 - 2 / x) * (ν / x) + ν / x ^ 2 = ν * (x - 1) / x ^ 2 := by
                    field_simp; ring
                  rw [this, div_le_div_iff₀ (by positivity) (by linarith)]
                  linear_combination hν0
                linarith
