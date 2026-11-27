-- Prove2me | solution 1 for ConjGrad.ErrorDecrease.Supplement.theorem_18_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:36:38.695799+00:00
-- url     : https://prove2.me/submissions/6edd56bb-3794-4b48-b230-5039257d4b9d

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_cfConv
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_smoothed

open Matrix

open ConjGrad
open ConjGrad.ErrorDecrease
open ConjGrad.ErrorDecrease.Supplement

/-- Theorem 18:2 (Hestenes–Stiefel 1952, p. 432): if `r₀ = k − Ax₀` is the sum of an orthonormal
system of eigenvectors of `A` with distinct eigenvalues, the characteristic polynomial of `A`
with respect to `r₀` is `χ'`, and the cg numbers are obtained by expanding the logarithmic
derivative `χ'/χ` into the normalized continued fraction (18:2), uniquely. -/
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ : Fin n → ℝ) (lam : Fin n → ℝ) (e : Fin n → Fin n → ℝ)
    (horth : ∀ i j, e i ⬝ᵥ e j = if i = j then 1 else 0)
    (heig : ∀ j, A *ᵥ e j = lam j • e j) (hdist : Function.Injective lam)
    (hr : (cgIter A k x₀ 0).r = ∑ j, e j) :
    relCharPoly A (cgIter A k x₀ 0).r = Polynomial.derivative A.charpoly ∧
    (cfConv (fun i => cgAlpha A (cgIter A k x₀ i)) (cgCoeffC A k x₀) n).2 =
        Polynomial.C (A.charpoly.eval 0)⁻¹ * A.charpoly ∧
    Polynomial.derivative A.charpoly * (cfConv (fun i => cgAlpha A (cgIter A k x₀ i)) (cgCoeffC A k x₀) n).2 =
      Polynomial.C (cgAlpha A (cgIter A k x₀ 0) * ((cgIter A k x₀ 0).r ⬝ᵥ (cgIter A k x₀ 0).r)) *
        (cfConv (fun i => cgAlpha A (cgIter A k x₀ i)) (cgCoeffC A k x₀) n).1 * A.charpoly ∧
    (∀ i : ℕ, i + 1 < n →
      ((cgIter A k x₀ (i + 1)).r ⬝ᵥ (cgIter A k x₀ (i + 1)).r) /
          ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) =
        cgCoeffC A k x₀ (i + 1) * cgAlpha A (cgIter A k x₀ i) /
          cgAlpha A (cgIter A k x₀ (i + 1))) ∧
    (0 < n → cgBeta A k x₀ (n - 1) = 0) ∧
    (∀ (a c : ℕ → ℝ) (κ : ℝ), (∀ i < n, a i ≠ 0) →
      Polynomial.derivative A.charpoly * (cfConv a c n).2 = Polynomial.C κ * (cfConv a c n).1 * A.charpoly →
      (0 < n → κ = cgAlpha A (cgIter A k x₀ 0) * ((cgIter A k x₀ 0).r ⬝ᵥ (cgIter A k x₀ 0).r)) ∧
      (∀ i < n, a i = cgAlpha A (cgIter A k x₀ i)) ∧
      ∀ i : ℕ, 0 < i → i < n → c i = cgCoeffC A k x₀ i) := by
        classical
        have hAT : Aᵀ = A := by simpa using hA.1.eq
        have hsym : ∀ v w : Fin n → ℝ, v ⬝ᵥ (A *ᵥ w) = (A *ᵥ v) ⬝ᵥ w := by
          intro v w
          rw [dotProduct_mulVec, ← mulVec_transpose, hAT]
        have hpos : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < v ⬝ᵥ (A *ᵥ v) := by
          intro v hv; simpa using hA.dotProduct_mulVec_pos hv
        obtain ⟨S, hS⟩ : ∃ S, S = cgIter A k x₀ := ⟨_, rfl⟩
        rw [← hS] at hr ⊢
        have Fr : ∀ i, (S (i+1)).r = (S i).r - cgAlpha A (S i) • (A *ᵥ (S i).p) := by
          subst hS; intro i; rfl
        have Fp : ∀ i, (S (i+1)).p = (S (i+1)).r +
            ((S (i+1)).r ⬝ᵥ (S (i+1)).r / ((S i).r ⬝ᵥ (S i).r)) • (S i).p := by
          subst hS; intro i; rfl
        have F0 : (S 0).p = (S 0).r := by subst hS; rfl
        have Fα : ∀ i, cgAlpha A (S i) = (S i).r ⬝ᵥ (S i).r / ((S i).p ⬝ᵥ (A *ᵥ (S i).p)) :=
          fun i => rfl
        have hrp0 : ∀ i, (S i).r = 0 → (S i).p = 0 := by
          intro i hi
          cases i with
          | zero => rw [F0, hi]
          | succ i => rw [Fp, hi]; simp
        have hαne : ∀ i, (S i).p ≠ 0 → cgAlpha A (S i) ≠ 0 := by
          intro i hp hα
          rw [Fα] at hα
          have := hpos _ hp
          rcases div_eq_zero_iff.mp hα with h | h
          · exact hp (hrp0 i (dotProduct_self_eq_zero.mp h))
          · linarith
        have Inv : ∀ i, (∀ j < i, (S i).r ⬝ᵥ (S j).r = 0 ∧ (S i).r ⬝ᵥ (S j).p = 0 ∧
            (S i).p ⬝ᵥ (A *ᵥ (S j).p) = 0) ∧ (S i).r ⬝ᵥ (S i).p = (S i).r ⬝ᵥ (S i).r := by
          intro i
          induction i with
          | zero => exact ⟨fun j hj => absurd hj (by omega), by rw [F0]⟩
          | succ i ih =>
            obtain ⟨ih, ihrp⟩ := ih
            have ha : ∀ j ≤ i, (S (i+1)).r ⬝ᵥ (S j).p = 0 := by
              intro j hj
              rw [Fr, sub_dotProduct, smul_dotProduct]
              rcases lt_or_eq_of_le hj with hj | rfl
              · rw [(ih j hj).2.1, ← hsym, (ih j hj).2.2]; simp
              · rw [← hsym, ihrp]
                by_cases hp : (S j).p = 0
                · have : (S j).r ⬝ᵥ (S j).r = 0 := by rw [← ihrp, hp]; simp
                  rw [this, hp]; simp
                · have := hpos _ hp
                  rw [smul_eq_mul, Fα, div_mul_cancel₀ _ this.ne', sub_self]
            have hb : ∀ j ≤ i, (S (i+1)).r ⬝ᵥ (S j).r = 0 := by
              intro j hj
              cases j with
              | zero => rw [← F0]; exact ha 0 hj
              | succ j =>
                have e1 : (S (j+1)).r = (S (j+1)).p -
                    ((S (j+1)).r ⬝ᵥ (S (j+1)).r / ((S j).r ⬝ᵥ (S j).r)) • (S j).p := by
                  rw [Fp]; abel
                rw [e1, dotProduct_sub, dotProduct_smul, ha _ hj, ha j (by omega)]; simp
            refine ⟨fun j hj => ⟨hb j (by omega), ha j (by omega), ?_⟩, ?_⟩
            · rw [Fp, add_dotProduct, smul_dotProduct]
              by_cases hp : (S j).p = 0
              · rw [hp]; simp
              have hαj := hαne j hp
              have key : cgAlpha A (S j) * ((S (i+1)).r ⬝ᵥ (A *ᵥ (S j).p)) =
                  (S (i+1)).r ⬝ᵥ (S j).r - (S (i+1)).r ⬝ᵥ (S (j+1)).r := by
                rw [Fr j, dotProduct_sub, dotProduct_smul]; simp
              rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
              · rw [(ih j hj).2.2, hb j (by omega), hb (j+1) (by omega), sub_zero] at *
                have : (S (i+1)).r ⬝ᵥ (A *ᵥ (S j).p) = 0 := by
                  rcases mul_eq_zero.mp key with h | h
                  · exact absurd h hαj
                  · exact h
                rw [this]; simp
              · rw [hb j le_rfl, zero_sub] at key
                have hr0 : (S j).r ⬝ᵥ (S j).r ≠ 0 := by
                  intro h; exact hp (hrp0 j (dotProduct_self_eq_zero.mp h))
                have := hpos _ hp
                have hx : (S (j+1)).r ⬝ᵥ (A *ᵥ (S j).p) = -((S (j+1)).r ⬝ᵥ (S (j+1)).r) / cgAlpha A (S j) :=
                  eq_div_of_mul_eq hαj (by rw [mul_comm]; linarith [key])
                rw [hx, smul_eq_mul, Fα]
                field_simp
                ring
            · rw [Fp, dotProduct_add, dotProduct_smul, ha i le_rfl]; simp
        open Polynomial in
        have cf2 : ∀ (a c : ℕ → ℝ) i, cfConv a c (i+2) =
            ((C (1 + c (i+1)) - C (a (i+1)) * X) * (cfConv a c (i+1)).1 - C (c (i+1)) * (cfConv a c i).1,
             (C (1 + c (i+1)) - C (a (i+1)) * X) * (cfConv a c (i+1)).2 - C (c (i+1)) * (cfConv a c i).2) :=
          fun a c i => rfl
        have cf0 : ∀ (a c : ℕ → ℝ), cfConv a c 0 = (0, 1) := fun a c => rfl
        have cf1 : ∀ (a c : ℕ → ℝ), cfConv a c 1 = (-1, 1 - Polynomial.C (a 0) * Polynomial.X) :=
          fun a c => rfl
        have hq : ∀ u v : ℝ, (Polynomial.C u - Polynomial.C v * Polynomial.X).natDegree ≤ 1 := by
          intro u v; compute_degree
        have GD : ∀ (a c : ℕ → ℝ) i, ((cfConv a c i).2.natDegree ≤ i ∧
            (cfConv a c i).2.coeff i = ∏ j ∈ Finset.range i, (-a j)) ∧
            ((cfConv a c (i+1)).2.natDegree ≤ i + 1 ∧
            (cfConv a c (i+1)).2.coeff (i+1) = ∏ j ∈ Finset.range (i+1), (-a j)) := by
          intro a c i
          induction i with
          | zero =>
            refine ⟨by simp [cf0], ?_⟩
            rw [cf1]
            refine ⟨?_, ?_⟩
            · simp only
              exact hq _ _
            · simp [Polynomial.coeff_one, Polynomial.coeff_C_mul, Polynomial.coeff_X]
          | succ i ih =>
            refine ⟨ih.2, ?_⟩
            obtain ⟨⟨d0, c0⟩, ⟨d1, c1⟩⟩ := ih
            rw [cf2]
            simp only
            refine ⟨?_, ?_⟩
            · refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
              · refine (Polynomial.natDegree_mul_le).trans ?_
                have := hq (1 + c (i + 1)) (a (i + 1))
                omega
              · refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
                omega
            · rw [Polynomial.coeff_sub, sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
                Polynomial.coeff_C_mul, mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul,
                Polynomial.coeff_eq_zero_of_natDegree_lt (show _ < i + 1 + 1 by omega),
                Polynomial.coeff_eq_zero_of_natDegree_lt (show _ < i + 1 + 1 by omega), c1,
                Finset.prod_range_succ _ (i+1)]
              ring
        have GE : ∀ (a c : ℕ → ℝ) i, (cfConv a c i).2.eval 0 = 1 ∧ (cfConv a c (i+1)).2.eval 0 = 1 := by
          intro a c i
          induction i with
          | zero => simp [cf0, cf1]
          | succ i ih =>
            refine ⟨ih.2, ?_⟩
            rw [cf2]; simp [ih.1, ih.2]
        have GW : ∀ (a c : ℕ → ℝ) i, ∃ w : ℝ, (cfConv a c (i+1)).1 * (cfConv a c i).2 -
            (cfConv a c i).1 * (cfConv a c (i+1)).2 = Polynomial.C w := by
          intro a c i
          induction i with
          | zero => exact ⟨-1, by simp [cf0, cf1]⟩
          | succ i ih =>
            obtain ⟨w, hw⟩ := ih
            refine ⟨c (i+1) * w, ?_⟩
            rw [cf2, Polynomial.C_mul, ← hw]; simp only; ring
        have GC : ∀ (a c a' c' : ℕ → ℝ), (∀ i < n, a i = a' i) → (∀ i, 0 < i → i < n → c i = c' i) →
            ∀ m, m + 1 ≤ n → cfConv a c m = cfConv a' c' m ∧ cfConv a c (m+1) = cfConv a' c' (m+1) := by
          intro a c a' c' ha hc m
          induction m with
          | zero => intro h; simp [cf0, cf1, ha 0 (by omega)]
          | succ m ih =>
            intro h
            obtain ⟨h1, h2⟩ := ih (by omega)
            refine ⟨h2, ?_⟩
            rw [cf2, cf2, h1, h2, ha (m+1) (by omega), hc (m+1) (by omega) (by omega)]
        obtain ⟨α, hα⟩ : ∃ α : ℕ → ℝ, α = fun i => cgAlpha A (S i) := ⟨_, rfl⟩
        rw [show (fun i => cgAlpha A (S i)) = α from hα.symm]
        have hαi : ∀ i, cgAlpha A (S i) = α i := fun i => by rw [hα]
        have hcC : ∀ i, cgCoeffC A k x₀ (i+1) =
            (S (i+1)).r ⬝ᵥ (S (i+1)).r / ((S i).r ⬝ᵥ (S i).r) * α (i+1) / α i := by
          intro i; rw [← hαi, ← hαi, hS]; rfl
        have hco : ∀ v l, (A *ᵥ v) ⬝ᵥ e l = lam l * (v ⬝ᵥ e l) := by
          intro v l; rw [← hsym, heig, dotProduct_smul, smul_eq_mul]
        have hr0e : ∀ l, (S 0).r ⬝ᵥ e l = 1 := by
          intro l; rw [hr, sum_dotProduct]; simp [horth]
        have Rep : ∀ i, (∀ j, j + 1 < i + 1 → α j ≠ 0) →
            (∀ l, (S i).r ⬝ᵥ e l = ((cfConv α (cgCoeffC A k x₀) i).2).eval (lam l)) ∧
            (∀ l, (S (i+1)).r ⬝ᵥ e l = ((cfConv α (cgCoeffC A k x₀) (i+1)).2).eval (lam l)) := by
          intro i
          induction i with
          | zero =>
            intro _
            refine ⟨fun l => by simp [cf0, hr0e], fun l => ?_⟩
            rw [cf1, Fr, sub_dotProduct, smul_dotProduct, hco, F0, hr0e, hαi]
            simp
          | succ i ih =>
            intro hne
            obtain ⟨h0, h1⟩ := ih (fun j hj => hne j (by omega))
            refine ⟨h1, fun l => ?_⟩
            have ha := hne i (by omega)
            have e1 := h1 l
            rw [Fr, sub_dotProduct, smul_dotProduct, hco, h0 l] at e1
            rw [cf2, Fr, sub_dotProduct, smul_dotProduct, hco, Fp, add_dotProduct, smul_dotProduct,
              h1 l, hcC]
            try simp only [hαi] at e1 ⊢
            simp only [smul_eq_mul, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
            set P := (S i).p ⬝ᵥ e l
            set x1 := (cfConv α (cgCoeffC A k x₀) (i + 1)).2.eval (lam l)
            set x0 := (cfConv α (cgCoeffC A k x₀) i).2.eval (lam l)
            simp only [smul_eq_mul] at e1
            have : lam l * P = (x0 - x1) / α i := by field_simp; linarith
            rw [mul_add, mul_add, mul_left_comm (lam l) _ P, this]
            field_simp
            ring
        have Nd : ∀ i < n, (S i).r ≠ 0 ∧ α i ≠ 0 := by
          intro i
          induction i using Nat.strong_induction_on with
          | _ i ih =>
            intro hi
            have hrep := (Rep i (fun j hj => (ih j (by omega) (by omega)).2)).1
            have hrne : (S i).r ≠ 0 := by
              intro h0
              have hz := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
                ((cfConv α (cgCoeffC A k x₀) i).2) hdist
                (fun l => by rw [← hrep l, h0, zero_dotProduct])
                (by simpa using lt_of_le_of_lt (GD α (cgCoeffC A k x₀) i).1.1 hi)
              have hc := (GD α (cgCoeffC A k x₀) i).1.2
              rw [hz, Polynomial.coeff_zero] at hc
              refine absurd hc.symm (Finset.prod_ne_zero_iff.mpr fun j hj => ?_)
              exact neg_ne_zero.mpr (ih j (Finset.mem_range.mp hj) (by have := Finset.mem_range.mp hj; omega)).2
            refine ⟨hrne, ?_⟩
            rw [← hαi]
            apply hαne
            intro hp
            have := (Inv i).2
            rw [hp, dotProduct_zero] at this
            exact hrne (dotProduct_self_eq_zero.mp this.symm)
        have hort : ∀ i j, i ≠ j → (S i).r ⬝ᵥ (S j).r = 0 := by
          intro i j hij
          rcases lt_or_gt_of_ne hij with h | h
          · rw [dotProduct_comm]; exact ((Inv j).1 i h).1
          · exact ((Inv i).1 j h).1
        have hrn : (S n).r = 0 := by
          let G : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i l => (S i.val).r l
          have hGG : G * Gᵀ = Matrix.diagonal (fun i => (S i.val).r ⬝ᵥ (S i.val).r) := by
            ext i j
            rw [mul_apply, diagonal_apply]
            by_cases hij : i = j
            · subst hij; simp [G, dotProduct]
            · rw [if_neg hij]
              have := hort i.val j.val (fun h => hij (Fin.ext h))
              simpa [G, dotProduct] using this
          have hdet : G.det ≠ 0 := by
            intro h
            have := congrArg Matrix.det hGG
            rw [det_mul, h, zero_mul, det_diagonal] at this
            exact absurd this.symm (Finset.prod_ne_zero_iff.mpr fun i _ => fun h0 =>
              (Nd i.val i.isLt).1 (dotProduct_self_eq_zero.mp h0))
          apply eq_zero_of_mulVec_eq_zero hdet
          ext i
          have := hort i.val n (by have := i.isLt; omega)
          simpa [G, mulVec, dotProduct] using this
        have hRn : ∀ l, ((cfConv α (cgCoeffC A k x₀) n).2).eval (lam l) = 0 := by
          intro l
          rcases Nat.eq_zero_or_pos n with h0 | hpos'
          · exact absurd l.isLt (by omega)
          · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
            rw [← (Rep m (fun j hj => (Nd j (by omega)).2)).2 l, hrn, zero_dotProduct]
        set χ := A.charpoly with hχdef
        have heu : ∀ j, e j ⬝ᵥ e j = 1 := fun j => by rw [horth]; simp
        have hene : ∀ j, e j ≠ 0 := fun j h => by have := heu j; rw [h, zero_dotProduct] at this; simp at this
        have hlpos : ∀ j, 0 < lam j := by
          intro j
          have := hpos (e j) (hene j)
          rwa [heig, dotProduct_smul, heu, smul_eq_mul, mul_one] at this
        have hχroot : ∀ j, χ.eval (lam j) = 0 := by
          intro j
          rw [hχdef, eval_charpoly]
          apply Matrix.exists_mulVec_eq_zero_iff.mp
          refine ⟨e j, hene j, ?_⟩
          rw [sub_mulVec, heig]; simp
        have hχnd : χ.natDegree = n := by rw [hχdef, charpoly_natDegree_eq_dim, Fintype.card_fin]
        have hχmon : χ.Monic := charpoly_monic A
        have hχne : χ ≠ 0 := hχmon.ne_zero
        have hPmon : (∏ j, (Polynomial.X - Polynomial.C (lam j))).Monic :=
          Polynomial.monic_prod_of_monic _ _ (fun j _ => Polynomial.monic_X_sub_C _)
        have hPnd : (∏ j, (Polynomial.X - Polynomial.C (lam j))).natDegree = n := by
          rw [Polynomial.natDegree_prod_of_monic _ _ (fun j _ => Polynomial.monic_X_sub_C _)]
          simp
        have hχprod : χ = ∏ j, (Polynomial.X - Polynomial.C (lam j)) := by
          by_contra hne
          have hne' : χ - ∏ j, (Polynomial.X - Polynomial.C (lam j)) ≠ 0 := sub_ne_zero.mpr hne
          have hdeg := Polynomial.degree_sub_lt (p := χ) (q := ∏ j, (Polynomial.X - Polynomial.C (lam j))) (by rw [Polynomial.degree_eq_natDegree hχne,
            Polynomial.degree_eq_natDegree hPmon.ne_zero, hχnd, hPnd]) hχne
            (by rw [hχmon.leadingCoeff, hPmon.leadingCoeff])
          rw [Polynomial.degree_eq_natDegree hχne, hχnd] at hdeg
          have hnd : (χ - ∏ j, (Polynomial.X - Polynomial.C (lam j))).natDegree < n :=
            (Polynomial.natDegree_lt_iff_degree_lt hne').mpr hdeg
          exact hne' (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hdist
            (fun l => by simp [hχroot, Polynomial.eval_prod, Finset.prod_eq_zero_iff]; exact ⟨l, sub_self _⟩)
            (by simpa using hnd))
        obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : Fin n → Polynomial ℝ, ℓ = fun j => ∏ k ∈ Finset.univ.erase j,
          (Polynomial.X - Polynomial.C (lam k)) := ⟨_, rfl⟩
        have hℓ : ∀ j, (Polynomial.X - Polynomial.C (lam j)) * ℓ j = χ := by
          intro j; rw [hχprod, hℓdef]
          exact Finset.mul_prod_erase Finset.univ (fun k => Polynomial.X - Polynomial.C (lam k)) (Finset.mem_univ j)
        have hℓmon : ∀ j, (ℓ j).Monic := fun j => by
          rw [hℓdef]; exact Polynomial.monic_prod_of_monic _ _ (fun k _ => Polynomial.monic_X_sub_C _)
        have hℓnd : ∀ j, (ℓ j).natDegree = n - 1 := by
          intro j
          rw [hℓdef]; simp only
          rw [Polynomial.natDegree_prod_of_monic _ _ (fun k _ => Polynomial.monic_X_sub_C _)]
          simp [Finset.card_erase_of_mem]
        have hℓev : ∀ j, (ℓ j).eval (lam j) ≠ 0 := by
          intro j
          rw [hℓdef]; simp only
          rw [Polynomial.eval_prod, Finset.prod_ne_zero_iff]
          intro k hk
          simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_ne_zero]
          exact fun h => (Finset.mem_erase.mp hk).1 (hdist h).symm
        have hℓev' : ∀ j k, k ≠ j → (ℓ j).eval (lam k) = 0 := by
          intro j k hkj
          rw [hℓdef]; simp only
          rw [Polynomial.eval_prod, Finset.prod_eq_zero_iff]
          exact ⟨k, Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ _⟩, by simp⟩
        have hχ' : Polynomial.derivative χ = ∑ j, ℓ j := by
          rw [hχprod, Polynomial.derivative_prod_finset]; simp [hℓdef]
        have hχ0 : χ.eval 0 ≠ 0 := by
          rw [hχprod, Polynomial.eval_prod, Finset.prod_ne_zero_iff]
          intro j _; simp; exact (hlpos j).ne'
        -- Λ
        obtain ⟨Λ, hΛdef⟩ : ∃ Λ : Polynomial ℝ → Polynomial ℝ,
          Λ = fun P => ∑ j, Polynomial.C (P.eval (lam j)) * ℓ j := ⟨_, rfl⟩
        have hΛq : ∀ (u v w : ℝ) (P Q : Polynomial ℝ),
            Λ ((Polynomial.C u - Polynomial.C v * Polynomial.X) * P - Polynomial.C w * Q) =
            (Polynomial.C u - Polynomial.C v * Polynomial.X) * Λ P - Polynomial.C w * Λ Q +
              Polynomial.C v * χ * Polynomial.C (∑ j, P.eval (lam j)) := by
          intro u v w P Q
          simp only [hΛdef, Finset.mul_sum, map_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← hℓ j]
          simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
            Polynomial.C_sub, Polynomial.C_mul]
          ring
        have hΛnd : ∀ P, (Λ P).natDegree ≤ n - 1 := by
          intro P
          rw [hΛdef]
          refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
          exact (Polynomial.natDegree_C_mul_le _ _).trans (hℓnd j).le
        have hΛc : ∀ P, (Λ P).coeff (n-1) = ∑ j, P.eval (lam j) := by
          intro P
          simp only [hΛdef, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← hℓnd j, (hℓmon j).coeff_natDegree, mul_one]
        have hdec : ∀ P, ∃ Q, Polynomial.derivative χ * P = χ * Q + Λ P := by
          intro P
          have : ∀ j, ∃ q, P - Polynomial.C (P.eval (lam j)) = (Polynomial.X - Polynomial.C (lam j)) * q := by
            intro j
            exact Polynomial.dvd_iff_isRoot.mpr (by simp)
          choose q hq using this
          refine ⟨∑ j, q j, ?_⟩
          simp only [hχ', hΛdef, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← hℓ j]
          have := hq j
          linear_combination (ℓ j) * this
        have hsmall : ∀ Q, (χ * Q).natDegree < n → Q = 0 := by
          intro Q hQ
          by_contra hQ0
          rw [Polynomial.natDegree_mul hχne hQ0, hχnd] at hQ
          omega
        have hr00 : (S 0).r ⬝ᵥ (S 0).r = n := by
          calc (S 0).r ⬝ᵥ (S 0).r = (S 0).r ⬝ᵥ (∑ j, e j) := by rw [← hr]
            _ = ∑ j, (S 0).r ⬝ᵥ e j := dotProduct_sum _ _ _
            _ = n := by simp [hr0e]
        have hL : ∀ l, 1 ≤ l → l < n →
            ∑ j, ((cfConv α (cgCoeffC A k x₀) l).2).eval (lam j) = 0 := by
          intro l h1 h2
          obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
          have hrep := (Rep m (fun j hj => (Nd j (by omega)).2)).2
          simp only [← hrep]
          rw [← dotProduct_sum, ← hr]
          exact hort _ _ (by omega)
        have hΛ0 : Λ 1 = Polynomial.derivative χ := by rw [hΛdef, hχ']; simp
        have St2 : ∀ m, m + 1 ≤ n →
            (Polynomial.derivative χ * (cfConv α (cgCoeffC A k x₀) m).2 - Λ (cfConv α (cgCoeffC A k x₀) m).2 =
              Polynomial.C (α 0 * ((S 0).r ⬝ᵥ (S 0).r)) * (cfConv α (cgCoeffC A k x₀) m).1 * χ) ∧
            (Polynomial.derivative χ * (cfConv α (cgCoeffC A k x₀) (m+1)).2 -
                Λ (cfConv α (cgCoeffC A k x₀) (m+1)).2 =
              Polynomial.C (α 0 * ((S 0).r ⬝ᵥ (S 0).r)) * (cfConv α (cgCoeffC A k x₀) (m+1)).1 * χ) := by
          intro m
          induction m with
          | zero =>
            intro _
            refine ⟨by simp [cf0, hΛ0], ?_⟩
            have e1 : (1 : Polynomial ℝ) - Polynomial.C (α 0) * Polynomial.X =
                (Polynomial.C 1 - Polynomial.C (α 0) * Polynomial.X) * 1 - Polynomial.C 0 * 0 := by simp
            rw [cf1]; simp only
            rw [e1, hΛq, hΛ0, hr00]
            simp only [Polynomial.eval_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul, mul_one, Polynomial.C_mul, map_natCast]
            simp
            ring
          | succ m ih =>
            intro hm
            obtain ⟨h0, h1⟩ := ih (by omega)
            refine ⟨h1, ?_⟩
            rw [cf2]; simp only
            rw [hΛq, hL (m+1) (by omega) (by omega)]
            simp only [map_zero, mul_zero, add_zero]
            linear_combination (Polynomial.C (1 + cgCoeffC A k x₀ (m + 1)) -
              Polynomial.C (α (m + 1)) * Polynomial.X) * h1 - Polynomial.C (cgCoeffC A k x₀ (m + 1)) * h0
        have hSt : Polynomial.derivative χ * (cfConv α (cgCoeffC A k x₀) n).2 - Λ (cfConv α (cgCoeffC A k x₀) n).2 =
              Polynomial.C (α 0 * ((S 0).r ⬝ᵥ (S 0).r)) * (cfConv α (cgCoeffC A k x₀) n).1 * χ := by
          rcases Nat.eq_zero_or_pos n with h0 | hpos'
          · subst h0; simp [cf0, hΛ0]
          · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
            exact (St2 m le_rfl).2
        have hΛn : Λ (cfConv α (cgCoeffC A k x₀) n).2 = 0 := by
          rw [hΛdef]; simp [hRn]
        have claim3 : Polynomial.derivative χ * (cfConv α (cgCoeffC A k x₀) n).2 =
            Polynomial.C (α 0 * ((S 0).r ⬝ᵥ (S 0).r)) * (cfConv α (cgCoeffC A k x₀) n).1 * χ := by
          rw [← hSt, hΛn, sub_zero]
        -- a polynomial of degree ≤ n vanishing at the λ_j with value 1 at 0
        have hnorm : ∀ P : Polynomial ℝ, P.natDegree ≤ n → (∀ l, P.eval (lam l) = 0) → P.eval 0 = 1 →
            P = Polynomial.C (χ.eval 0)⁻¹ * χ := by
          intro P hd hz h0
          rw [← sub_eq_zero]
          let f : Option (Fin n) → ℝ := fun o => o.elim 0 lam
          have hf : Function.Injective f := by
            intro o1 o2 h
            rcases o1 with _ | a <;> rcases o2 with _ | b <;>
              simp only [f, Option.elim_none, Option.elim_some] at h
            · rfl
            · exact absurd h.symm (hlpos b).ne'
            · exact absurd h (hlpos a).ne'
            · rw [hdist h]
          apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hf
          · intro o
            cases o with
            | none => simp [f, h0, hχ0]
            | some l => simp [f, hz, hχroot]
          · simp only [Fintype.card_option, Fintype.card_fin]
            refine lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) ?_
            refine lt_of_le_of_lt (max_le hd ((Polynomial.natDegree_C_mul_le _ _).trans hχnd.le)) ?_
            omega
        have claim2 : (cfConv α (cgCoeffC A k x₀) n).2 = Polynomial.C (χ.eval 0)⁻¹ * χ :=
          hnorm _ (GD α _ n).1.1 hRn (GE α _ n).1
        have claim4 : ∀ i : ℕ, i + 1 < n →
            ((S (i + 1)).r ⬝ᵥ (S (i + 1)).r) / ((S i).r ⬝ᵥ (S i).r) =
              cgCoeffC A k x₀ (i + 1) * cgAlpha A (S i) / cgAlpha A (S (i + 1)) := by
          intro i hi
          rw [hcC, hαi, hαi]
          have h1 := (Nd i (by omega)).2
          have h2 := (Nd (i+1) hi).2
          field_simp
        have claim5 : 0 < n → cgBeta A k x₀ (n - 1) = 0 := by
          intro hn
          have : cgBeta A k x₀ (n - 1) = (S (n - 1 + 1)).r ⬝ᵥ (S (n - 1 + 1)).r /
              ((S (n-1)).r ⬝ᵥ (S (n-1)).r) := by rw [hS]; rfl
          rw [this, Nat.sub_add_cancel hn, hrn]; simp
        have hχ'ev : ∀ l, (Polynomial.derivative χ).eval (lam l) ≠ 0 := by
          intro l
          rw [hχ', Polynomial.eval_finset_sum, Finset.sum_eq_single l (fun j _ hj => hℓev' j l (Ne.symm hj))
            (fun h => absurd (Finset.mem_univ l) h)]
          exact hℓev l
        have hOrth : ∀ (a c : ℕ → ℝ), (∀ i < n, a i ≠ 0) →
            (∀ l, 1 ≤ l → l < n → ∑ j, (cfConv a c l).2.eval (lam j) = 0) →
            (∀ j, (cfConv a c n).2.eval (lam j) = 0) →
            ∀ m l, m < l → l ≤ n → ∑ j, lam j ^ m * (cfConv a c l).2.eval (lam j) = 0 := by
          intro a c ha hL0 hn0 m
          induction m with
          | zero =>
            intro l hl hln
            rcases lt_or_eq_of_le hln with h | rfl
            · simpa using hL0 l hl h
            · simp [hn0]
          | succ m ih =>
            intro l hl hln
            rcases lt_or_eq_of_le hln with h | rfl
            · obtain ⟨j, rfl⟩ : ∃ j, l = j + 1 + 1 := ⟨l - 2, by omega⟩
              have e := congrArg Prod.snd (cf2 a c (j+1))
              have h1 := ih (j+1+1) (by omega) h.le
              have h0 := ih (j+1) (by omega) (by omega)
              have h3 := ih (j+1+2) (by omega) (by omega)
              have hne := ha (j+1+1) h
              have key : a (j+1+1) * ∑ t, lam t ^ (m+1) * (cfConv a c (j+1+1)).2.eval (lam t) =
                  (1 + c (j+1+1)) * ∑ t, lam t ^ m * (cfConv a c (j+1+1)).2.eval (lam t) -
                  c (j+1+1) * ∑ t, lam t ^ m * (cfConv a c (j+1)).2.eval (lam t) -
                  ∑ t, lam t ^ m * (cfConv a c (j+1+2)).2.eval (lam t) := by
                rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
                  ← Finset.sum_sub_distrib]
                refine Finset.sum_congr rfl fun t _ => ?_
                rw [e]
                simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
                ring
              rw [h1, h0, h3] at key
              simp only [mul_zero, sub_zero] at key
              exact (mul_eq_zero.mp key).resolve_left hne
            · simp [hn0]
        have hUniq : ∀ (a c a' c' : ℕ → ℝ),
            (∀ m l, m < l → l ≤ n → ∑ j, lam j ^ m * (cfConv a c l).2.eval (lam j) = 0) →
            (∀ m l, m < l → l ≤ n → ∑ j, lam j ^ m * (cfConv a' c' l).2.eval (lam j) = 0) →
            ∀ l ≤ n, (cfConv a c l).2 = (cfConv a' c' l).2 := by
          intro a c a' c' ho ho' l hl
          rcases Nat.eq_zero_or_pos l with rfl | hl0
          · simp [cf0]
          rw [← sub_eq_zero]
          obtain ⟨D, hD⟩ : ∃ D, D = (cfConv a c l).2 - (cfConv a' c' l).2 := ⟨_, rfl⟩
          rw [← hD]
          have hD0 : D.eval 0 = 0 := by simp [hD, (GE a c l).1, (GE a' c' l).1]
          obtain ⟨D₁, hD₁⟩ : Polynomial.X ∣ D :=
            Polynomial.X_dvd_iff.mpr (by rw [Polynomial.coeff_zero_eq_eval_zero, hD0])
          have hDnd : D.natDegree ≤ l := by
            rw [hD]; exact (Polynomial.natDegree_sub_le_of_le (GD a c l).1.1 (GD a' c' l).1.1).trans (max_self l).le
          have hD1nd : D₁.natDegree < l := by
            by_cases h : D₁ = 0
            · rw [h, Polynomial.natDegree_zero]; omega
            · rw [hD₁, Polynomial.natDegree_mul Polynomial.X_ne_zero h, Polynomial.natDegree_X] at hDnd
              omega
          have hmom : ∀ m < l, ∑ j, lam j ^ m * D.eval (lam j) = 0 := by
            intro m hm
            simp only [hD, Polynomial.eval_sub, mul_sub, Finset.sum_sub_distrib, ho m l hm hl,
              ho' m l hm hl, sub_self]
          have hsum : ∑ j, lam j * (D₁.eval (lam j)) ^ 2 = 0 := by
            have : ∀ j, lam j * (D₁.eval (lam j)) ^ 2 = D.eval (lam j) * D₁.eval (lam j) := by
              intro j; rw [hD₁]; simp; ring
            simp_rw [this]
            simp_rw [Polynomial.eval_eq_sum_range' hD1nd, Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_eq_zero fun m hm => ?_
            have := hmom m (Finset.mem_range.mp hm)
            calc ∑ j, D.eval (lam j) * (D₁.coeff m * lam j ^ m)
                = D₁.coeff m * ∑ j, lam j ^ m * D.eval (lam j) := by
                  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
              _ = 0 := by rw [this, mul_zero]
          have hz : ∀ j, D₁.eval (lam j) = 0 := by
            intro j
            have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hlpos j).le
              (sq_nonneg _))).mp hsum j (Finset.mem_univ _)
            rcases mul_eq_zero.mp this with h | h
            · exact absurd h (hlpos j).ne'
            · exact pow_eq_zero_iff (by norm_num) |>.mp h
          have : D₁ = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero D₁ hdist hz
            (by simpa using lt_of_lt_of_le hD1nd hl)
          rw [hD₁, this, mul_zero]
        have claim6 : ∀ (a c : ℕ → ℝ) (κ : ℝ), (∀ i < n, a i ≠ 0) →
            Polynomial.derivative χ * (cfConv a c n).2 = Polynomial.C κ * (cfConv a c n).1 * χ →
            (0 < n → κ = α 0 * ((S 0).r ⬝ᵥ (S 0).r)) ∧ (∀ i < n, a i = α i) ∧
            ∀ i : ℕ, 0 < i → i < n → c i = cgCoeffC A k x₀ i := by
          intro a c κ ha H
          have U1 : ∀ l, (cfConv a c n).2.eval (lam l) = 0 := by
            intro l
            have := congrArg (Polynomial.eval (lam l)) H
            simp only [Polynomial.eval_mul, hχroot l, mul_zero] at this
            exact (mul_eq_zero.mp this).resolve_left (hχ'ev l)
          obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℕ → Polynomial ℝ, Φ = fun i => Polynomial.C κ * (cfConv a c i).1 * χ -
              Polynomial.derivative χ * (cfConv a c i).2 := ⟨_, rfl⟩
          have hΦW : ∀ i, ∃ w, Φ i * (cfConv a c (i+1)).2 - Φ (i+1) * (cfConv a c i).2 =
              Polynomial.C w * χ := by
            intro i
            obtain ⟨w, hw⟩ := GW a c i
            refine ⟨-(κ * w), ?_⟩
            rw [hΦ, map_neg, Polynomial.C_mul]
            linear_combination (-(Polynomial.C κ) * χ) * hw
          have hRnd : ∀ i < n, (cfConv a c (i+1)).2.natDegree = i + 1 := by
            intro i hi
            refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (GD a c i).2.1 ?_
            rw [(GD a c i).2.2, Finset.prod_ne_zero_iff]
            intro j hj
            exact neg_ne_zero.mpr (ha j (by have := Finset.mem_range.mp hj; omega))
          have hRne : ∀ i, (cfConv a c i).2 ≠ 0 := by
            intro i h; have := (GE a c i).1; rw [h] at this; simp at this
          have hdown : ∀ t, t ≤ n → Φ (n - t) = 0 ∨ (Φ (n - t)).natDegree + (n - t) < n := by
            intro t
            induction t with
            | zero => intro _; left; rw [hΦ]; simp only [Nat.sub_zero]; rw [H]; ring
            | succ t ih =>
              intro ht
              have ih' := ih (by omega)
              obtain ⟨w, hw⟩ := hΦW (n - (t+1))
              have e : n - (t+1) + 1 = n - t := by omega
              rw [e] at hw
              by_cases h0 : Φ (n - (t+1)) = 0
              · left; exact h0
              right
              have hR := hRnd (n - (t+1)) (by omega)
              rw [e] at hR
              have hle : (Φ (n - (t+1)) * (cfConv a c (n - t)).2).natDegree ≤ n := by
                rw [eq_add_of_sub_eq hw]
                refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
                · exact (Polynomial.natDegree_C_mul_le _ _).trans hχnd.le
                · rcases ih' with h | h
                  · rw [h, zero_mul, Polynomial.natDegree_zero]; omega
                  · refine Polynomial.natDegree_mul_le.trans ?_
                    have := (GD a c (n - (t+1))).1.1
                    omega
              rw [Polynomial.natDegree_mul h0 (hRne _), hR] at hle
              omega
          have U3 : ∀ l, 1 ≤ l → l < n → ∑ j, (cfConv a c l).2.eval (lam j) = 0 := by
            intro l h1 h2
            have hd := hdown (n - l) (by omega)
            rw [show n - (n - l) = l by omega] at hd
            obtain ⟨Q, hQ⟩ := hdec (cfConv a c l).2
            have hid : χ * (Polynomial.C κ * (cfConv a c l).1 - Q) = Φ l + Λ (cfConv a c l).2 := by
              rw [hΦ]; simp only; linear_combination hQ
            have hz : Polynomial.C κ * (cfConv a c l).1 - Q = 0 := by
              apply hsmall
              rw [hid]
              refine lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt ?_ ?_)
              · rcases hd with h | h
                · rw [h, Polynomial.natDegree_zero]; omega
                · omega
              · exact lt_of_le_of_lt (hΛnd _) (by omega)
            rw [hz, mul_zero] at hid
            have hΛe : Λ (cfConv a c l).2 = -Φ l := by linear_combination -hid
            rw [← hΛc, hΛe, Polynomial.coeff_neg, neg_eq_zero]
            rcases hd with h | h
            · rw [h, Polynomial.coeff_zero]
            · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
          have hoA := hOrth a c ha U3 U1
          have hoC := hOrth α (cgCoeffC A k x₀) (fun i hi => (Nd i hi).2) hL hRn
          have hEq := hUniq α (cgCoeffC A k x₀) a c hoC hoA
          have hAeq : ∀ i < n, a i = α i := by
            intro i hi
            have e1 := (GD a c i).2.2
            have e0 := (GD a c i).1.2
            have f1 := (GD α (cgCoeffC A k x₀) i).2.2
            have f0 := (GD α (cgCoeffC A k x₀) i).1.2
            rw [← hEq (i+1) hi] at e1
            rw [← hEq i hi.le] at e0
            have g1 := e1.symm.trans f1
            have g0 := e0.symm.trans f0
            rw [Finset.prod_range_succ, Finset.prod_range_succ, g0] at g1
            have hP0 : ∏ j ∈ Finset.range i, (-α j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j hj =>
              neg_ne_zero.mpr (Nd j (by have := Finset.mem_range.mp hj; omega)).2
            have := mul_left_cancel₀ hP0 g1
            linarith
          have hCeq : ∀ i : ℕ, 0 < i → i < n → c i = cgCoeffC A k x₀ i := by
            intro i h0 hi
            obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
            have e := congrArg Prod.snd (cf2 a c j)
            have f := congrArg Prod.snd (cf2 α (cgCoeffC A k x₀) j)
            simp only at e f
            rw [← hEq (j+2) (by omega), ← hEq (j+1) (by omega), ← hEq j (by omega), hAeq (j+1) hi] at e
            have hdiff : (cfConv α (cgCoeffC A k x₀) (j+1)).2 - (cfConv α (cgCoeffC A k x₀) j).2 ≠ 0 := by
              intro h
              have := congrArg (fun p => p.coeff (j+1)) h
              simp only [Polynomial.coeff_sub, Polynomial.coeff_zero] at this
              rw [(GD α _ j).2.2, Polynomial.coeff_eq_zero_of_natDegree_lt
                (lt_of_le_of_lt (GD α (cgCoeffC A k x₀) j).1.1 (Nat.lt_succ_self j)), sub_zero] at this
              refine (Finset.prod_ne_zero_iff.mpr fun t ht => ?_) this
              exact neg_ne_zero.mpr (Nd t (by have := Finset.mem_range.mp ht; omega)).2
            have : Polynomial.C (c (j+1) - cgCoeffC A k x₀ (j+1)) *
                ((cfConv α (cgCoeffC A k x₀) (j+1)).2 - (cfConv α (cgCoeffC A k x₀) j).2) = 0 := by
              simp only [map_add, map_one, map_sub] at e f ⊢
              linear_combination f - e
            rcases mul_eq_zero.mp this with h | h
            · exact sub_eq_zero.mp (Polynomial.C_eq_zero.mp h)
            · exact absurd h hdiff
          refine ⟨fun hn => ?_, hAeq, hCeq⟩
          have hcf := (GC a c α (cgCoeffC A k x₀) hAeq hCeq (n-1) (by omega)).2
          rw [Nat.sub_add_cancel hn] at hcf
          rw [hcf] at H
          have h2 := H.symm.trans claim3
          have hN : (cfConv α (cgCoeffC A k x₀) n).1 ≠ 0 := by
            intro h
            rw [h, mul_zero, zero_mul] at claim3
            rcases mul_eq_zero.mp claim3 with h' | h'
            · exact hχ'ev ⟨0, hn⟩ (by rw [h', Polynomial.eval_zero])
            · have := (GE α (cgCoeffC A k x₀) n).1; rw [h'] at this; simp at this
          have h3 : Polynomial.C (κ - α 0 * ((S 0).r ⬝ᵥ (S 0).r)) *
              ((cfConv α (cgCoeffC A k x₀) n).1 * χ) = 0 := by
            rw [Polynomial.C_sub]; linear_combination h2
          rcases mul_eq_zero.mp h3 with h | h
          · exact sub_eq_zero.mp (Polynomial.C_eq_zero.mp h)
          · rcases mul_eq_zero.mp h with h' | h'
            · exact absurd h' hN
            · exact absurd h' hχne
        have claim1 : relCharPoly A (S 0).r = Polynomial.derivative χ := by
          obtain ⟨Q, hQ⟩ : ∃ Q, Q = adjugate (charmatrix A) := ⟨_, rfl⟩
          let eh : Fin n → Fin n → Polynomial ℝ := fun j l => Polynomial.C (e j l)
          let rh : Fin n → Polynomial ℝ := fun l => Polynomial.C ((S 0).r l)
          have hstepa : relCharPoly A (S 0).r = rh ⬝ᵥ (Q *ᵥ rh) := by
            simp only [relCharPoly, hQ, dotProduct, mulVec, Finset.mul_sum, rh, Polynomial.C_mul]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
          have hstepb : ∀ j, charmatrix A *ᵥ eh j = (Polynomial.X - Polynomial.C (lam j)) • eh j := by
            intro j
            funext i
            have hi := congrFun (heig j) i
            simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hi ⊢
            simp only [charmatrix_apply, sub_mul, Finset.sum_sub_distrib, diagonal_apply, ite_mul,
              zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, eh]
            simp_rw [← Polynomial.C_mul]
            rw [← map_sum, hi, Polynomial.C_mul]
          have hstepc : ∀ j, (Polynomial.X - Polynomial.C (lam j)) • (Q *ᵥ eh j) = χ • eh j := by
            intro j
            rw [← mulVec_smul, ← hstepb, mulVec_mulVec, hQ, adjugate_mul, smul_mulVec, one_mulVec]
            rfl
          have hrh : ∀ j, rh ⬝ᵥ eh j = 1 := by
            intro j
            have := hr0e j
            simp only [dotProduct, rh, eh, ← Polynomial.C_mul, ← map_sum] at this ⊢
            rw [this, map_one]
          have hstepd : ∀ j, rh ⬝ᵥ (Q *ᵥ eh j) = ℓ j := by
            intro j
            have h := congrArg (fun v => rh ⬝ᵥ v) (hstepc j)
            simp only [dotProduct_smul, smul_eq_mul, hrh, mul_one] at h
            rw [← hℓ j] at h
            exact mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero _) h
          have hrsum : rh = ∑ j, eh j := by
            ext l
            simp [rh, eh, hr, Finset.sum_apply, map_sum]
          rw [hstepa, hχ']
          conv_lhs => rw [hrsum]
          rw [mulVec_sum, dotProduct_sum, ← hrsum]
          exact Finset.sum_congr rfl fun j _ => hstepd j
        refine ⟨claim1, claim2, ?_, claim4, claim5, ?_⟩
        · rw [hαi]; exact claim3
        · intro a c κ ha H
          have := claim6 a c κ ha H
          simp only [hαi]
          exact this
