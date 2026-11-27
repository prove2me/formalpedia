-- Prove2me | solution 1 for ConjGrad.ErrorDecrease.Supplement.theorem_7_5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:34:46.857964+00:00
-- url     : https://prove2.me/submissions/1cf57a44-4435-4b54-b0d7-0db66416bafd

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_smoothed

open Matrix

open ConjGrad
open ConjGrad.ErrorDecrease
open ConjGrad.ErrorDecrease.Supplement

/-- Theorem 7:5 (Hestenes–Stiefel 1952, p. 419): `|yᵢ| < |ȳᵢ|` for `0 < i < m` and
`|ȳᵢ| < |ȳᵢ₋₁|` for `1 ≤ i ≤ m`, where `yᵢ = h − xᵢ`, `ȳᵢ = h − x̄ᵢ` and `m` is the step at which
the cg-method terminates; at `i = 0` and `i = m` the two error vectors coincide. Corrected: the
paper prints "`ȳᵢ` is shorter than `yᵢ₋₁`", which is false; its proof gives `|ȳᵢ| < |ȳᵢ₋₁|`. -/
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ h : Fin n → ℝ) (hh : A *ᵥ h = k) (m : ℕ) (hm : (cgIter A k x₀ m).r = 0)
    (hact : ∀ j < m, (cgIter A k x₀ j).r ≠ 0) :
    (∀ i : ℕ, 0 < i → i < m →
      (h - (cgIter A k x₀ i).x) ⬝ᵥ (h - (cgIter A k x₀ i).x) <
        (h - smoothX A k x₀ i) ⬝ᵥ (h - smoothX A k x₀ i)) ∧
    (∀ i : ℕ, i + 1 ≤ m →
      (h - smoothX A k x₀ (i + 1)) ⬝ᵥ (h - smoothX A k x₀ (i + 1)) <
        (h - smoothX A k x₀ i) ⬝ᵥ (h - smoothX A k x₀ i)) ∧
    smoothX A k x₀ 0 = (cgIter A k x₀ 0).x ∧ smoothX A k x₀ m = (cgIter A k x₀ m).x := by
      have hsym : ∀ u v : Fin n → ℝ, u ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ u) := by
        intro u v
        have hT : Aᵀ = A := by
          have := hA.1
          rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
        rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, dotProduct_comm]
      have hpos : ∀ w : Fin n → ℝ, w ≠ 0 → 0 < w ⬝ᵥ (A *ᵥ w) := by
        intro w hw
        simpa using hA.dotProduct_mulVec_pos hw
      have hnn : ∀ w : Fin n → ℝ, 0 ≤ w ⬝ᵥ (A *ᵥ w) := by
        intro w
        by_cases hw : w = 0
        · simp [hw]
        · exact (hpos w hw).le
      have hself : ∀ w : Fin n → ℝ, 0 ≤ w ⬝ᵥ w := fun w =>
        Finset.sum_nonneg (fun i _ => mul_self_nonneg (w i))
      have hzero : ∀ w : Fin n → ℝ, w ⬝ᵥ w = 0 → w = 0 := fun w hw => dotProduct_self_eq_zero.mp hw
      suffices key : ∀ (X R P : ℕ → (Fin n → ℝ)) (α β C : ℕ → ℝ) (Xb : ℕ → (Fin n → ℝ)),
          X 0 = x₀ → R 0 = k - A *ᵥ X 0 → P 0 = R 0 →
          (∀ i, α i = R i ⬝ᵥ R i / (P i ⬝ᵥ (A *ᵥ P i))) →
          (∀ i, β i = R (i+1) ⬝ᵥ R (i+1) / (R i ⬝ᵥ R i)) →
          (∀ i, X (i+1) = X i + α i • P i) →
          (∀ i, R (i+1) = R i - α i • (A *ᵥ P i)) →
          (∀ i, P (i+1) = R (i+1) + β i • P i) →
          C 0 = 1 → Xb 0 = x₀ →
          (∀ i, C (i+1) = 1 + β i * C i) →
          (∀ i, Xb (i+1) = (1 + β i * C i)⁻¹ • (X (i+1) + (β i * C i) • Xb i)) →
          R m = 0 → (∀ j < m, R j ≠ 0) →
        (∀ i : ℕ, 0 < i → i < m → (h - X i) ⬝ᵥ (h - X i) < (h - Xb i) ⬝ᵥ (h - Xb i)) ∧
        (∀ i : ℕ, i + 1 ≤ m → (h - Xb (i + 1)) ⬝ᵥ (h - Xb (i + 1)) < (h - Xb i) ⬝ᵥ (h - Xb i)) ∧
        Xb 0 = X 0 ∧ Xb m = X m by
        exact key (fun i => (cgIter A k x₀ i).x) (fun i => (cgIter A k x₀ i).r)
          (fun i => (cgIter A k x₀ i).p) (fun i => cgAlpha A (cgIter A k x₀ i))
          (fun i => cgBeta A k x₀ i) (fun i => smoothC A k x₀ i) (fun i => smoothX A k x₀ i)
          rfl rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
          rfl rfl (fun _ => rfl) (fun _ => rfl)
          hm hact
      intro X R P α β C Xb hX0 hR0 hP0 hα hβ hX hRs hPs hC0 hXb0 hCs hXbs hm hact
      have hRX : ∀ i, R i = k - A *ᵥ X i := by
        intro i
        induction i with
        | zero => exact hR0
        | succ i ih =>
          rw [hRs, hX, ih, Matrix.mulVec_add, Matrix.mulVec_smul]; abel
      have hAE : ∀ i, A *ᵥ (h - X i) = R i := by
        intro i; rw [Matrix.mulVec_sub, hh, hRX]
      have hRP0 : ∀ i, R i = 0 → P i = 0 := by
        intro i hi
        cases i with
        | zero => rw [hP0, hi]
        | succ i => rw [hPs, hβ, hi]; simp
      have hαP : ∀ i, α i = 0 → P i = 0 := by
        intro i hi
        rw [hα, div_eq_zero_iff] at hi
        rcases hi with hi | hi
        · exact hRP0 i (hzero _ hi)
        · by_contra hne
          exact (hpos _ hne).ne' hi
      have hQ : ∀ i, (∀ j < i, R i ⬝ᵥ P j = 0 ∧ R i ⬝ᵥ R j = 0 ∧ P i ⬝ᵥ (A *ᵥ P j) = 0) ∧
          R i ⬝ᵥ P i = R i ⬝ᵥ R i := by
        intro i
        induction i with
        | zero => exact ⟨fun j hj => absurd hj (Nat.not_lt_zero _), by rw [hP0]⟩
        | succ i ih =>
          obtain ⟨ih1, ih2⟩ := ih
          have hii : R (i+1) ⬝ᵥ P i = 0 := by
            by_cases hp : P i = 0
            · rw [hp]; simp
            · have hpp := hpos _ hp
              rw [hRs, sub_dotProduct, smul_dotProduct, dotProduct_comm (A *ᵥ P i), ih2, hα]
              simp only [smul_eq_mul]
              field_simp
              ring
          have ha : ∀ j < i + 1, R (i+1) ⬝ᵥ P j = 0 := by
            intro j hj
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
            · rw [hRs, sub_dotProduct, smul_dotProduct, dotProduct_comm (A *ᵥ P i), ← hsym,
                (ih1 j hj).1, (ih1 j hj).2.2]
              simp
            · rw [hj]; exact hii
          have hb : ∀ j < i + 1, R (i+1) ⬝ᵥ R j = 0 := by
            intro j hj
            cases j with
            | zero => rw [← hP0]; exact ha 0 hj
            | succ j =>
              have e : R (j+1) = P (j+1) - β j • P j := by rw [hPs]; abel
              rw [e, dotProduct_sub, dotProduct_smul, ha _ hj, ha j (by omega)]
              simp
          have hRA' : ∀ j < i, R (i+1) ⬝ᵥ (A *ᵥ P j) = 0 := by
            intro j hj
            by_cases h0 : α j = 0
            · rw [hαP j h0]; simp
            · have e : α j • (A *ᵥ P j) = R j - R (j+1) := by rw [hRs]; abel
              have : α j * (R (i+1) ⬝ᵥ (A *ᵥ P j)) = 0 := by
                rw [← smul_eq_mul, ← dotProduct_smul, e, dotProduct_sub, hb j (by omega),
                  hb (j+1) (by omega)]
                simp
              rcases mul_eq_zero.mp this with h1 | h1
              · exact absurd h1 h0
              · exact h1
          refine ⟨fun j hj => ⟨ha j hj, hb j hj, ?_⟩, ?_⟩
          · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
            · rw [hPs, add_dotProduct, smul_dotProduct, hRA' j hj, (ih1 j hj).2.2]; simp
            · subst hj
              by_cases h0 : α j = 0
              · rw [hαP j h0]; simp
              · have e : α j • (A *ᵥ P j) = R j - R (j+1) := by rw [hRs]; abel
                have h1 : α j * (R (j+1) ⬝ᵥ (A *ᵥ P j)) = - (R (j+1) ⬝ᵥ R (j+1)) := by
                  rw [← smul_eq_mul, ← dotProduct_smul, e, dotProduct_sub, hb j (by omega)]
                  simp
                have hp : P j ≠ 0 := by
                  intro hp; apply h0; rw [hα, hp]; simp
                have hpp := hpos _ hp
                have hrr : R j ⬝ᵥ R j ≠ 0 := by
                  intro hr; apply h0; rw [hα, hr]; simp
                rw [hPs, add_dotProduct, smul_dotProduct, hβ, smul_eq_mul]
                rw [hα] at h1
                field_simp at h1 ⊢
                linear_combination h1
          · rw [hPs, dotProduct_add, dotProduct_smul, hii]; simp
      have hRRpos : ∀ i < m, 0 < R i ⬝ᵥ R i := by
        intro i hi
        rcases (hself (R i)).lt_or_eq with h1 | h1
        · exact h1
        · exact absurd (hzero _ h1.symm) (hact i hi)
      have hPne : ∀ i < m, P i ≠ 0 := by
        intro i hi hp
        have hr := hRRpos i hi
        have := (hQ i).2
        rw [hp] at this; simp at this; linarith
      have hαpos : ∀ i < m, 0 < α i := by
        intro i hi
        rw [hα]; exact div_pos (hRRpos i hi) (hpos _ (hPne i hi))
      have hβnn : ∀ i, 0 ≤ β i := fun i => by rw [hβ]; exact div_nonneg (hself _) (hself _)
      have hβpos : ∀ i, i + 1 < m → 0 < β i := fun i hi => by
        rw [hβ]; exact div_pos (hRRpos _ hi) (hRRpos _ (by omega))
      -- positivity of the Gram matrix of the directions
      have hpp : ∀ s, s < m → ∀ l ≤ s, 0 < P l ⬝ᵥ P s := by
        intro s
        induction s with
        | zero =>
          intro hs l hl
          have hl0 : l = 0 := by omega
          subst hl0
          rcases (hself (P 0)).lt_or_eq with h1 | h1
          · exact h1
          · exact absurd (hzero _ h1.symm) (hPne 0 hs)
        | succ s ih =>
          intro hs l hl
          rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hl) with hl | hl
          · have h0 : P l ⬝ᵥ R (s+1) = 0 := by
              rw [dotProduct_comm]; exact ((hQ (s+1)).1 l (by omega)).1
            rw [hPs, dotProduct_add, dotProduct_smul, h0, smul_eq_mul]
            have := ih (by omega) l (by omega)
            have := hβpos s hs
            positivity
          · subst hl
            rcases (hself (P (s+1))).lt_or_eq with h1 | h1
            · exact h1
            · exact absurd (hzero _ h1.symm) (hPne _ hs)
      have hG : ∀ l s, l < m → s < m → 0 < P l ⬝ᵥ P s := by
        intro l s hl hs
        rcases le_total l s with h1 | h1
        · exact hpp s hs l h1
        · rw [dotProduct_comm]; exact hpp l hl s h1
      -- the cone spanned by the directions
      let K : (Fin n → ℝ) → Prop := fun v =>
        ∃ c : ℕ → ℝ, (∀ s, 0 ≤ c s) ∧ v = ∑ s ∈ Finset.range m, c s • P s
      have hK0 : K 0 := ⟨fun _ => 0, fun _ => le_refl _, by simp⟩
      have hKadd : ∀ u v, K u → K v → K (u + v) := by
        rintro u v ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
        refine ⟨fun s => c s + d s, fun s => add_nonneg (hc s) (hd s), ?_⟩
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun s _ => (add_smul _ _ _).symm)
      have hKsmul : ∀ (t : ℝ) u, 0 ≤ t → K u → K (t • u) := by
        rintro t u ht ⟨c, hc, rfl⟩
        refine ⟨fun s => t * c s, fun s => mul_nonneg ht (hc s), ?_⟩
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl (fun s _ => (mul_smul _ _ _).symm)
      have hKP : ∀ l < m, K (P l) := by
        intro l hl
        refine ⟨fun s => if s = l then 1 else 0, fun s => by dsimp only; split_ifs <;> norm_num, ?_⟩
        simp [ite_smul, Finset.mem_range, hl]
      have hKdot : ∀ u v, K u → K v → 0 ≤ u ⬝ᵥ v := by
        rintro u v ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
        rw [sum_dotProduct]
        apply Finset.sum_nonneg
        intro s hs
        rw [dotProduct_sum]
        apply Finset.sum_nonneg
        intro t ht
        rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
        have := (hG s t (Finset.mem_range.mp hs) (Finset.mem_range.mp ht)).le
        have := hc s
        have := hd t
        positivity
      have hKpos : ∀ l s, l < m → s < m → ∀ c d : ℝ, 0 < c → 0 < d → ∀ u v, K u → K v →
          0 < (c • P l + u) ⬝ᵥ (d • P s + v) := by
        intro l s hl hs c d hc hd u v hu hv
        have e : (c • P l + u) ⬝ᵥ (d • P s + v) =
            c * d * (P l ⬝ᵥ P s) + (c * (P l ⬝ᵥ v) + (d * (u ⬝ᵥ P s) + u ⬝ᵥ v)) := by
          simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
          ring
        rw [e]
        have h1 := hG l s hl hs
        have h2 := hKdot _ _ (hKP l hl) hv
        have h3 := hKdot _ _ hu (hKP s hs)
        have h4 := hKdot _ _ hu hv
        positivity
      -- the final iterate is the solution
      have hXm : X m = h := by
        have e := hAE m
        rw [hm] at e
        by_contra hne
        have hne' : h - X m ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
        have := hpos _ hne'
        rw [e] at this; simp at this
      have hXd : ∀ i d, i + d ≤ m → K (X (i + d) - X i) := by
        intro i d
        induction d with
        | zero => intro _; simpa using hK0
        | succ d ih =>
          intro hd
          have e : X (i + (d+1)) - X i = (X (i + d) - X i) + α (i+d) • P (i+d) := by
            rw [← add_assoc, hX]; abel
          rw [e]
          exact hKadd _ _ (ih (by omega)) (hKsmul _ _ (hαpos _ (by omega)).le (hKP _ (by omega)))
      have hy : ∀ i ≤ m, K (h - X i) := by
        intro i hi
        have := hXd i (m - i) (by omega)
        rwa [show i + (m - i) = m by omega, hXm] at this
      have hy' : ∀ i, h - X i = α i • P i + (h - X (i+1)) := by
        intro i; rw [hX]; abel
      -- the weights c_i
      have hC1 : ∀ i, 1 ≤ C i := by
        intro i
        induction i with
        | zero => rw [hC0]
        | succ i ih =>
          rw [hCs]
          have := hβnn i
          have : 0 ≤ β i * C i := mul_nonneg this (by linarith)
          linarith
      have hstep : ∀ i, ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ (0 < β i → 0 < θ) ∧
          X (i+1) - Xb (i+1) = θ • (α i • P i + (X i - Xb i)) := by
        intro i
        have hq : 0 ≤ β i * C i := mul_nonneg (hβnn i) (by linarith [hC1 i])
        refine ⟨β i * C i / (1 + β i * C i), div_nonneg hq (by linarith), ?_, ?_, ?_⟩
        · rw [div_lt_one (by linarith)]; linarith
        · intro hb
          have : 0 < β i * C i := mul_pos hb (by linarith [hC1 i])
          positivity
        · rw [hXbs, hX]
          have hne : (1 + β i * C i) ≠ 0 := by linarith
          ext j
          simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          field_simp
          ring
      have hD : ∀ i ≤ m, K (X i - Xb i) := by
        intro i
        induction i with
        | zero => intro _; rw [hX0, hXb0, sub_self]; exact hK0
        | succ i ih =>
          intro hi
          obtain ⟨θ, hθ0, _, _, e⟩ := hstep i
          rw [e]
          exact hKsmul _ _ hθ0 (hKadd _ _ (hKsmul _ _ (hαpos i (by omega)).le (hKP i (by omega)))
            (ih (by omega)))
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i hi0 him
        obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        obtain ⟨θ, hθ0, _, hθp, e⟩ := hstep j
        have hθ := hθp (hβpos j him)
        have hpos2 : 0 < (h - X (j+1)) ⬝ᵥ (X (j+1) - Xb (j+1)) := by
          rw [hy' (j+1), e, smul_add, smul_smul]
          exact hKpos _ _ him (by omega) _ _ (hαpos _ him) (mul_pos hθ (hαpos _ (by omega)))
            _ _ (hy _ (by omega)) (hKsmul _ _ hθ0 (hD j (by omega)))
        have e2 : h - Xb (j+1) = (h - X (j+1)) + (X (j+1) - Xb (j+1)) := by abel
        rw [e2]
        have h3 := hKdot _ _ (hD (j+1) (by omega)) (hD (j+1) (by omega))
        simp only [add_dotProduct, dotProduct_add] at h3 ⊢
        rw [dotProduct_comm (X (j+1) - Xb (j+1)) (h - X (j+1))]
        linarith
      · intro i hi
        obtain ⟨θ, hθ0, hθ1, _, e⟩ := hstep i
        have eA : (h - Xb i) - (h - Xb (i+1)) =
            ((1 - θ) * α i) • P i + (1 - θ) • (X i - Xb i) := by
          have : (h - Xb i) - (h - Xb (i+1)) =
              (α i • P i + (X i - Xb i)) - (X (i+1) - Xb (i+1)) := by rw [hX]; abel
          rw [this, e]
          module
        have eB : (h - Xb i) + (h - Xb (i+1)) =
            α i • P i + (((h - X (i+1)) + (X i - Xb i)) + ((h - X (i+1)) + (X (i+1) - Xb (i+1)))) := by
          rw [hX]; abel
        have hmain : 0 < ((h - Xb i) - (h - Xb (i+1))) ⬝ᵥ ((h - Xb i) + (h - Xb (i+1))) := by
          rw [eA, eB]
          exact hKpos _ _ (by omega) (by omega) _ _ (mul_pos (by linarith) (hαpos i (by omega)))
            (hαpos i (by omega)) _ _ (hKsmul _ _ (by linarith) (hD i (by omega)))
            (hKadd _ _ (hKadd _ _ (hy _ (by omega)) (hD i (by omega)))
              (hKadd _ _ (hy _ (by omega)) (hD (i+1) (by omega))))
        have e3 : ((h - Xb i) - (h - Xb (i+1))) ⬝ᵥ ((h - Xb i) + (h - Xb (i+1))) =
            (h - Xb i) ⬝ᵥ (h - Xb i) - (h - Xb (i+1)) ⬝ᵥ (h - Xb (i+1)) := by
          have gen : ∀ Y Y' : Fin n → ℝ, (Y - Y') ⬝ᵥ (Y + Y') = Y ⬝ᵥ Y - Y' ⬝ᵥ Y' := by
            intro Y Y'
            simp only [sub_dotProduct, dotProduct_add]
            rw [dotProduct_comm Y' Y]
            ring
          exact gen _ _
        linarith
      · rw [hXb0, hX0]
      · cases m with
        | zero => rw [hXb0, hX0]
        | succ j =>
          have hb : β j = 0 := by rw [hβ, hm]; simp
          rw [hXbs, hb]; simp
