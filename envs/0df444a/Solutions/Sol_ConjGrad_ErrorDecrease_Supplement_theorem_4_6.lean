-- Prove2me | solution 1 for ConjGrad.ErrorDecrease.Supplement.theorem_4_6
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:30:58.953237+00:00
-- url     : https://prove2.me/submissions/c7332885-33f8-4c89-b05e-6df58508bc50

import Mathlib
import Definitions.Def_ConjGrad_Termination_IsCDRun
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_errorFun
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_cdPlane

open Matrix

open ConjGrad
open ConjGrad.ErrorDecrease
open ConjGrad.ErrorDecrease.Supplement

/-- Theorem 4:6 (Hestenes–Stiefel 1952, p. 414). First part: every run of the cd-method.
`conjPlane A p (x i) i` is the plane `πᵢ` through `xᵢ` conjugate to `p₀, …, pᵢ₋₁`, with
direction space `conjDir A p i`; `Eᵢ'` is its intersection with the level set
`f(x) = f(xᵢ)`. Second part: the cg-method. -/
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k h : Fin n → ℝ) (hh : A *ᵥ h = k) :
    (∀ (x r p : ℕ → Fin n → ℝ), Termination.IsCDRun A k x r p → ∀ i : ℕ,
      ((∀ j < i, p j ≠ 0) → Module.finrank ℝ (conjDir A p i) = n - i) ∧
      (∀ j, i ≤ j → x j ∈ conjPlane A p (x i) i) ∧
      h ∈ conjPlane A p (x i) i ∧
      {y | y ∈ conjPlane A p (x i) i ∧ errorFun A h y = errorFun A h (x i)} =
        {y | ∃ v ∈ conjDir A p i, y = h + v ∧ v ⬝ᵥ (A *ᵥ v) = errorFun A h (x i)} ∧
      ((2 : ℝ) • x (i + 1) - x i ∈ conjPlane A p (x i) i ∧
        errorFun A h ((2 : ℝ) • x (i + 1) - x i) = errorFun A h (x i)) ∧
      (∃ t : ℝ, (2 : ℝ) • x (i + 1) - x i = x i + t • p i) ∧
      (∀ t : ℝ, x i + t • p i ∈ conjPlane A p (x i) i →
        errorFun A h (x i + t • p i) = errorFun A h (x i) →
        x i + t • p i = x i ∨ x i + t • p i = (2 : ℝ) • x (i + 1) - x i)) ∧
    (∀ (x₀ : Fin n → ℝ) (i : ℕ),
      (cgIter A k x₀ i).p ∈ conjDir A (fun j => (cgIter A k x₀ j).p) i ∧
      (∀ v ∈ conjDir A (fun j => (cgIter A k x₀ j).p) i,
        fderiv ℝ (errorFun A h) (cgIter A k x₀ i).x v = 0 → (cgIter A k x₀ i).p ⬝ᵥ v = 0) ∧
      ∃ c : ℝ, ∀ v ∈ conjDir A (fun j => (cgIter A k x₀ j).p) i,
        fderiv ℝ (errorFun A h) (cgIter A k x₀ i).x v = c * ((cgIter A k x₀ i).p ⬝ᵥ v)) := by
          classical
          have hs : Aᵀ = A := (Matrix.isHermitian_iff_isSymm.mp hA.isHermitian)
          have sym (u v : Fin n → ℝ) : u ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ u) := by
            rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hs, dotProduct_comm]
          have pos (v : Fin n → ℝ) (hv : v ≠ 0) : 0 < v ⬝ᵥ (A *ᵥ v) := by
            simpa using hA.dotProduct_mulVec_pos hv
          have mem (p : ℕ → Fin n → ℝ) (i : ℕ) (v : Fin n → ℝ) :
              v ∈ conjDir A p i ↔ ∀ j < i, p j ⬝ᵥ (A *ᵥ v) = 0 := by
            simp only [conjDir, LinearMap.mem_ker, Matrix.mulVecLin_apply, funext_iff,
              Matrix.mulVec, Matrix.of_apply, Pi.zero_apply]
            constructor
            · intro hv j hj
              rw [sym, dotProduct_comm]
              exact hv ⟨j, hj⟩
            · intro hv j
              change (A *ᵥ p j) ⬝ᵥ v = 0
              rw [dotProduct_comm, ← sym]
              exact hv j j.isLt
          have quad (z v : Fin n → ℝ) (t : ℝ) :
              errorFun A h (z + t • v) = errorFun A h z -
                2 * t * (v ⬝ᵥ (A *ᵥ (h - z))) + t ^ 2 * (v ⬝ᵥ (A *ᵥ v)) := by
            have he : h - (z + t • v) = (h - z) - t • v := by abel
            simp only [errorFun, he, Matrix.mulVec_sub, Matrix.mulVec_smul,
              sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
            rw [sym h v, sym z v]
            ring
          have deriv (z v : Fin n → ℝ) :
              fderiv ℝ (errorFun A h) z v = -2 * ((A *ᵥ (h - z)) ⬝ᵥ v) := by
            let B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ :=
              (LinearMap.toContinuousLinearMap.toLinearMap.comp A.toBilin').toContinuousLinearMap
            have hB (u v : Fin n → ℝ) : B u v = u ⬝ᵥ (A *ᵥ v) := by
              change A.toBilin' u v = _
              exact Matrix.toBilin'_apply' A u v
            have hf : HasFDerivAt (fun y : Fin n → ℝ => h - y)
                (-ContinuousLinearMap.id ℝ (Fin n → ℝ)) z := by
              simpa using (hasFDerivAt_const (𝕜 := ℝ) h z).sub (hasFDerivAt_id (𝕜 := ℝ) z)
            have hd := B.hasFDerivAt_of_bilinear hf hf
            have hefun : (fun y => B (h - y) (h - y)) = errorFun A h := by
              funext y
              exact hB _ _
            rw [hefun] at hd
            rw [hd.fderiv]
            simp only [_root_.add_apply, ContinuousLinearMap.precompR_apply,
              ContinuousLinearMap.precompL_apply, ContinuousLinearMap.compL_apply,
              ContinuousLinearMap.comp_apply, _root_.neg_apply,
              ContinuousLinearMap.id_apply, hB, Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct]
            rw [sym (h - z) v, dotProduct_comm (A *ᵥ (h - z)) v]
            ring
          have cdconj (x r p : ℕ → Fin n → ℝ) (run : Termination.IsCDRun A k x r p)
              (i j : ℕ) (hij : j < i) : p i ⬝ᵥ (A *ᵥ p j) = 0 := by
            cases i with
            | zero => omega
            | succ i => exact run.conj i j (by omega)
          have cdres (x r p : ℕ → Fin n → ℝ) (run : Termination.IsCDRun A k x r p) :
              ∀ i j, j < i → p j ⬝ᵥ r i = 0 := by
            intro i
            induction i with
            | zero => intro j hj; omega
            | succ i ih =>
              intro j hj
              have hr : r (i + 1) = r i -
                  ((p i ⬝ᵥ r i) / (p i ⬝ᵥ (A *ᵥ p i))) • (A *ᵥ p i) := by
                rw [run.residual (i + 1), run.step i, Matrix.mulVec_add, Matrix.mulVec_smul,
                  run.residual i]
                abel
              rw [hr, dotProduct_sub, dotProduct_smul, smul_eq_mul]
              by_cases hji : j < i
              · rw [ih j hji, sym (p j) (p i), cdconj x r p run i j hji]
                ring
              · have hji : j = i := by omega
                subst j
                by_cases hp : p i = 0
                · simp [hp]
                · rw [div_mul_cancel₀ _ (ne_of_gt (pos (p i) hp))]
                  ring
          constructor
          · intro x r p run i
            have hpdir (j : ℕ) (hij : i ≤ j) : p j ∈ conjDir A p i := by
              apply (mem p i (p j)).2
              intro l hl
              rw [sym]
              exact cdconj x r p run j l (by omega)
            have hfuture : ∀ j, i ≤ j → x j - x i ∈ conjDir A p i := by
              intro j hj
              induction j, hj using Nat.le_induction with
              | base => simp
              | succ j hj ih =>
                rw [run.step j]
                have he : x j + ((p j ⬝ᵥ r j) / (p j ⬝ᵥ (A *ᵥ p j))) • p j - x i =
                    (x j - x i) + ((p j ⬝ᵥ r j) / (p j ⬝ᵥ (A *ᵥ p j))) • p j := by abel
                rw [he]
                exact (conjDir A p i).add_mem ih ((conjDir A p i).smul_mem _ (hpdir j hj))
            have hsol : h - x i ∈ conjDir A p i := by
              apply (mem p i _).2
              intro j hj
              rw [Matrix.mulVec_sub, hh, ← run.residual i]
              exact cdres x r p run i j hj
            have href : (2 : ℝ) • x (i + 1) - x i =
                x i + (2 * ((p i ⬝ᵥ r i) / (p i ⬝ᵥ (A *ᵥ p i)))) • p i := by
              rw [run.step i]
              module
            have herr (t : ℝ) : errorFun A h (x i + t • p i) = errorFun A h (x i) -
                2 * t * (p i ⬝ᵥ r i) + t ^ 2 * (p i ⬝ᵥ (A *ᵥ p i)) := by
              rw [quad, Matrix.mulVec_sub, hh, ← run.residual i]
            have hlevel : errorFun A h ((2 : ℝ) • x (i + 1) - x i) = errorFun A h (x i) := by
              rw [href, herr]
              by_cases hp : p i = 0
              · simp [hp]
              · field_simp [ne_of_gt (pos (p i) hp)]
                ring
            refine ⟨?_, hfuture, hsol, ?_, ⟨?_, hlevel⟩, ⟨_, href⟩, ?_⟩
            · intro hn
              let f : (Fin n → ℝ) →ₗ[ℝ] (Fin i → ℝ) :=
                Matrix.mulVecLin (Matrix.of fun (j : Fin i) (l : Fin n) => (A *ᵥ p j) l)
              have hf (v : Fin n → ℝ) (j : Fin i) : f v j = p j ⬝ᵥ (A *ᵥ v) := by
                change (A *ᵥ p j) ⬝ᵥ v = _
                rw [dotProduct_comm, sym]
              have ho (j l : Fin i) (hjl : j ≠ l) : p j ⬝ᵥ (A *ᵥ p l) = 0 := by
                have hne : (j : ℕ) ≠ (l : ℕ) := fun he => hjl (Fin.ext he)
                rcases lt_or_gt_of_ne hne with hlt | hgt
                · rw [sym]
                  exact cdconj x r p run l j hlt
                · exact cdconj x r p run j l hgt
              have hf_surj : Function.Surjective f := by
                intro y
                refine ⟨∑ j : Fin i, (y j / (p j ⬝ᵥ (A *ᵥ p j))) • p j, ?_⟩
                ext l
                rw [hf]
                simp only [Matrix.mulVec_sum, dotProduct_sum, Matrix.mulVec_smul,
                  dotProduct_smul, smul_eq_mul]
                rw [Finset.sum_eq_single l]
                · exact div_mul_cancel₀ _ (ne_of_gt (pos (p l) (hn l l.isLt)))
                · intro j _ hj
                  rw [ho l j (Ne.symm hj), mul_zero]
                · simp
              have hdim := f.finrank_range_add_finrank_ker
              rw [LinearMap.range_eq_top.mpr hf_surj] at hdim
              simp only [finrank_top, Module.finrank_pi, Fintype.card_fin] at hdim
              change Module.finrank ℝ (LinearMap.ker f) = n - i
              omega
            · ext y
              change (y - x i ∈ conjDir A p i ∧ _) ↔ _
              constructor
              · rintro ⟨hy, he⟩
                have hv : y - h ∈ conjDir A p i := by
                  have heq : y - h = (y - x i) - (h - x i) := by abel
                  rw [heq]
                  exact (conjDir A p i).sub_mem hy hsol
                refine ⟨y - h, hv, ?_, ?_⟩
                · abel
                · have hn : h - y = -(y - h) := by abel
                  simpa only [errorFun, hn, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg] using he
              · rintro ⟨v, hv, rfl, he⟩
                constructor
                · have heq : h + v - x i = (h - x i) + v := by abel
                  rw [heq]
                  exact (conjDir A p i).add_mem hsol hv
                · simpa [errorFun, show h - (h + v) = -v by abel,
                    Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg] using he
            · change _ - x i ∈ conjDir A p i
              rw [href, add_sub_cancel_left]
              exact (conjDir A p i).smul_mem _ (hpdir i le_rfl)
            · intro t _ he
              by_cases hp : p i = 0
              · left; simp [hp]
              · have hd := ne_of_gt (pos (p i) hp)
                have heq : t * (t * (p i ⬝ᵥ (A *ᵥ p i)) - 2 * (p i ⬝ᵥ r i)) = 0 := by
                  rw [herr] at he
                  nlinarith
                rcases mul_eq_zero.mp heq with ht | ht
                · left; simp [ht]
                · right
                  rw [href]
                  have ht' : t = 2 * ((p i ⬝ᵥ r i) / (p i ⬝ᵥ (A *ᵥ p i))) := by
                    rw [← mul_div_assoc]
                    apply (eq_div_iff hd).2
                    nlinarith
                  rw [ht']
          · intro x₀ i
            let x : ℕ → Fin n → ℝ := fun j => (cgIter A k x₀ j).x
            let r : ℕ → Fin n → ℝ := fun j => (cgIter A k x₀ j).r
            let p : ℕ → Fin n → ℝ := fun j => (cgIter A k x₀ j).p
            let a : ℕ → ℝ := fun j => (r j ⬝ᵥ r j) / (p j ⬝ᵥ (A *ᵥ p j))
            let b : ℕ → ℝ := fun j => (r (j + 1) ⬝ᵥ r (j + 1)) / (r j ⬝ᵥ r j)
            have hx (j : ℕ) : x (j + 1) = x j + a j • p j := by rfl
            have hr (j : ℕ) : r (j + 1) = r j - a j • (A *ᵥ p j) := by rfl
            have hp (j : ℕ) : p (j + 1) = r (j + 1) + b j • p j := by rfl
            have hp0 : p 0 = r 0 := rfl
            have rz (j : ℕ) (hz : r j = 0) : p j = 0 := by
              cases j with
              | zero => exact hp0.trans hz
              | succ j => simp only [hp, b, hz, zero_dotProduct, zero_div, zero_smul, add_zero]
            have rorth (v : Fin n → ℝ) (m : ℕ) (hv : ∀ j ≤ m, v ⬝ᵥ p j = 0) :
                ∀ j ≤ m, v ⬝ᵥ r j = 0 := by
              intro j hj
              cases j with
              | zero => rw [← hp0]; exact hv 0 hj
              | succ j =>
                have he := congrArg (fun u => v ⬝ᵥ u) (hp j)
                simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at he
                rw [hv (j + 1) hj, hv j (by omega)] at he
                linarith
            have inv : ∀ m : ℕ,
                p m ⬝ᵥ r m = r m ⬝ᵥ r m ∧
                (∀ j < m, r m ⬝ᵥ p j = 0) ∧
                (∀ j < m, p m ⬝ᵥ (A *ᵥ p j) = 0) := by
              intro m
              induction m using Nat.strong_induction_on with
              | h m ih =>
                cases m with
                | zero => exact ⟨by rw [hp0], by omega, by omega⟩
                | succ m =>
                  obtain ⟨hpr, hor, hcon⟩ := ih m (by omega)
                  have hn : ∀ j ≤ m, r (m + 1) ⬝ᵥ p j = 0 := by
                    intro j hj
                    rw [hr, sub_dotProduct, smul_dotProduct, smul_eq_mul,
                      dotProduct_comm (A *ᵥ p m) (p j)]
                    by_cases hjm : j < m
                    · rw [hor j hjm, sym (p j) (p m), hcon j hjm]
                      ring
                    · have he : j = m := by omega
                      subst j
                      rw [dotProduct_comm (r m) (p m), hpr]
                      by_cases hz : r m = 0
                      · simp [hz, rz m hz]
                      · have hpn : p m ≠ 0 := by
                          intro he
                          have := hpr
                          rw [he, zero_dotProduct] at this
                          exact hz (dotProduct_self_eq_zero.mp this.symm)
                        dsimp only [a]
                        rw [div_mul_cancel₀ _ (ne_of_gt (pos (p m) hpn))]
                        ring
                  have hnr := rorth (r (m + 1)) m hn
                  have hcon' : ∀ j < m + 1, p (m + 1) ⬝ᵥ (A *ᵥ p j) = 0 := by
                    intro j hj
                    rw [hp, add_dotProduct, smul_dotProduct, smul_eq_mul]
                    by_cases hjm : j < m
                    · rw [hcon j hjm, mul_zero, add_zero]
                      by_cases hz : r j = 0
                      · simp [rz j hz]
                      · obtain ⟨hpj, _, _⟩ := ih j (by omega)
                        have hrr : r j ⬝ᵥ r j ≠ 0 := fun he => hz (dotProduct_self_eq_zero.mp he)
                        have hpjn : p j ≠ 0 := by
                          intro he
                          rw [he, zero_dotProduct] at hpj
                          exact hrr hpj.symm
                        have han : a j ≠ 0 := div_ne_zero hrr (ne_of_gt (pos (p j) hpjn))
                        have he := congrArg (fun u => r (m + 1) ⬝ᵥ u) (hr j)
                        simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul] at he
                        rw [hnr (j + 1) (by omega), hnr j (by omega)] at he
                        exact (mul_eq_zero.mp (by linarith : a j *
                          (r (m + 1) ⬝ᵥ (A *ᵥ p j)) = 0)).resolve_left han
                    · have hjm : j = m := by omega
                      subst j
                      by_cases hz : r m = 0
                      · simp [rz m hz]
                      · have hrr : r m ⬝ᵥ r m ≠ 0 := fun he => hz (dotProduct_self_eq_zero.mp he)
                        have hpn : p m ≠ 0 := by
                          intro he
                          rw [he, zero_dotProduct] at hpr
                          exact hrr hpr.symm
                        have hD := ne_of_gt (pos (p m) hpn)
                        have han : a m ≠ 0 := div_ne_zero hrr hD
                        have ha : a m * (p m ⬝ᵥ (A *ᵥ p m)) = r m ⬝ᵥ r m := div_mul_cancel₀ _ hD
                        have hb : b m * (r m ⬝ᵥ r m) = r (m + 1) ⬝ᵥ r (m + 1) :=
                          div_mul_cancel₀ _ hrr
                        have he := congrArg (fun u => r (m + 1) ⬝ᵥ u) (hr m)
                        simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul] at he
                        rw [hnr m le_rfl] at he
                        have heq : a m * (r (m + 1) ⬝ᵥ (A *ᵥ p m) +
                            b m * (p m ⬝ᵥ (A *ᵥ p m))) = 0 := by
                          calc
                            _ = a m * (r (m + 1) ⬝ᵥ (A *ᵥ p m)) +
                                b m * (a m * (p m ⬝ᵥ (A *ᵥ p m))) := by ring
                            _ = 0 := by rw [ha, hb]; linarith
                        exact (mul_eq_zero.mp heq).resolve_left han
                  refine ⟨?_, (fun j hj => hn j (by omega)), hcon'⟩
                  rw [hp, add_dotProduct, smul_dotProduct, smul_eq_mul,
                    dotProduct_comm (p m) (r (m + 1)), hn m le_rfl]
                  ring
            have residual : ∀ j, r j = k - A *ᵥ x j := by
              intro j
              induction j with
              | zero => rfl
              | succ j ih =>
                rw [hr, hx, ih, Matrix.mulVec_add, Matrix.mulVec_smul]
                abel
            have self_nonneg (v : Fin n → ℝ) : 0 ≤ v ⬝ᵥ v := by
              simpa using dotProduct_star_self_nonneg v
            have ratio : ∀ m, ∃ c : ℝ, 0 < c ∧ ∀ v ∈ conjDir A p m,
                r m ⬝ᵥ v = c * (p m ⬝ᵥ v) := by
              intro m
              induction m with
              | zero => exact ⟨1, by norm_num, by intro v _; rw [hp0, one_mul]⟩
              | succ m ih =>
                obtain ⟨c, hc, he⟩ := ih
                have hb : 0 ≤ b m := div_nonneg (self_nonneg _) (self_nonneg _)
                have hcb : 0 < c + b m := by linarith
                refine ⟨c / (c + b m), div_pos hc hcb, ?_⟩
                intro v hv
                have hv' : v ∈ conjDir A p m := (mem p m v).2 (fun j hj =>
                  (mem p (m + 1) v).1 hv j (by omega))
                have hvp : (A *ᵥ p m) ⬝ᵥ v = 0 := by
                  rw [dotProduct_comm, ← sym]
                  exact (mem p (m + 1) v).1 hv m (by omega)
                have he' : r (m + 1) ⬝ᵥ v = c * (p m ⬝ᵥ v) := by
                  rw [hr, sub_dotProduct, smul_dotProduct, smul_eq_mul, hvp, mul_zero, sub_zero]
                  exact he v hv'
                rw [hp, add_dotProduct, smul_dotProduct, smul_eq_mul, he']
                field_simp [ne_of_gt hcb]
            obtain ⟨c, hc, hratio⟩ := ratio i
            have hder (v : Fin n → ℝ) (hv : v ∈ conjDir A p i) :
                fderiv ℝ (errorFun A h) (x i) v = (-2 * c) * (p i ⬝ᵥ v) := by
              rw [deriv, Matrix.mulVec_sub, hh, ← residual i, hratio v hv]
              ring
            change p i ∈ conjDir A p i ∧ _
            refine ⟨(mem p i (p i)).2 ?_, ?_, ⟨-2 * c, ?_⟩⟩
            · intro j hj
              rw [sym]
              exact (inv i).2.2 j hj
            · intro v hv hd
              change p i ⬝ᵥ v = 0
              change fderiv ℝ (errorFun A h) (x i) v = 0 at hd
              rw [hder v hv] at hd
              exact (mul_eq_zero.mp hd).resolve_left (mul_ne_zero (by norm_num) (ne_of_gt hc))
            · intro v hv
              exact hder v hv
