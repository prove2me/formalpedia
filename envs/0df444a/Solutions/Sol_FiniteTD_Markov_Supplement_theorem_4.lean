-- Prove2me | solution 1 for FiniteTD.Markov.Supplement.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:13:21.136458+00:00
-- url     : https://prove2.me/submissions/3cac552b-9eed-474e-ab4f-5418ff8488ae

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting
import Definitions.Def_FiniteTD_Markov_Supplement_MeanPathIid
import Definitions.Def_FiniteTD_Markov_Supplement_Lambda

open FiniteTD
open FiniteTD.Markov
open FiniteTD.Markov.Supplement

theorem solution {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {d : ℕ} [NeZero d]
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (rmax γ lam : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (ω m ρ R : ℝ) (θstar θ0 : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (hRw : ∀ s s', |Rw s s'| ≤ rmax)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hφ : ∀ s, ‖φ s‖ ≤ 1) (hω : IsMinEig π φ ω) (hω0 : 0 < ω)
    (hfix : valFn φ θstar = projD π φ (Tlam P γ lam Rw (valFn φ θstar)))
    (hA1 : Assumption1 P π m ρ) (hR : ‖θstar‖ ≤ R) (hθ0 : ‖θ0‖ ≤ R) :
    -- (a) constant step size 1/√T, averaged iterate
    (∀ T : ℕ, 1 ≤ T → ∀ α : ℕ → ℝ, (∀ t ≤ T, α t = 1 / Real.sqrt T) →
      pathExp π P T (fun w =>
          dNormSq π φ (θstar - avgSeq (ptdLam γ lam Rw φ R α θ0 (extendPath w)) T)) ≤
        (‖θstar - θ0‖ ^ 2 + ((rmax + 2 * R) / (1 - γ * lam)) ^ 2
            * (13 + 28 * (tauMixLam m ρ (γ * lam) (1 / Real.sqrt T) : ℝ)))
          / (2 * Real.sqrt T * (1 - kappa γ lam))) ∧
    -- (b) constant step size α₀ < 1/(2ω(1-κ)) and T > 2τmix_λ(α₀), last iterate
    (∀ α0 : ℝ, 0 < α0 → α0 < 1 / (2 * ω * (1 - kappa γ lam)) →
      ∀ T : ℕ, 2 * tauMixLam m ρ (γ * lam) α0 < T → ∀ α : ℕ → ℝ, (∀ t ≤ T, α t = α0) →
      pathExp π P T (fun w => ‖θstar - ptdLam γ lam Rw φ R α θ0 (extendPath w) T‖ ^ 2) ≤
        Real.exp (-2 * α0 * (1 - kappa γ lam) * ω * T) * ‖θstar - θ0‖ ^ 2
          + α0 * (((rmax + 2 * R) / (1 - γ * lam)) ^ 2
              * (13 + 24 * (tauMixLam m ρ (γ * lam) α0 : ℝ)) / (2 * (1 - kappa γ lam) * ω))) ∧
    -- (c) decaying step size 1/(ω(t+1)(1-κ)), averaged iterate
    (∀ T : ℕ, 1 ≤ T → ∀ α : ℕ → ℝ,
      (∀ t : ℕ, α t = 1 / (ω * ((t : ℝ) + 1) * (1 - kappa γ lam))) →
      pathExp π P T (fun w =>
          dNormSq π φ (θstar - avgSeq (ptdLam γ lam Rw φ R α θ0 (extendPath w)) T)) ≤
        ((rmax + 2 * R) / (1 - γ * lam)) ^ 2
            * (13 + 52 * (tauMixLam m ρ (γ * lam) (α T) : ℝ)) / (T * (1 - kappa γ lam) ^ 2 * ω)
          * (1 + Real.log T)) := by
            classical
            have step :
              ∀ (P : S → S → ℝ) (π : S → ℝ) (T : ℕ) (G : (Fin (T + 1 + 1) → S) → ℝ),
                pathExp π P (T + 1) G = pathExp π P T (fun w => ∑ x, P (w (Fin.last T)) x * G (Fin.snoc (α := fun _ => S) w x)) := by
              intro P π T G
              unfold pathExp
              rw [← (Fin.snocEquiv (fun _ : Fin (T + 1 + 1) => S)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
              refine Finset.sum_congr rfl fun w _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun x _ => ?_
              have h0 : pathProb π P (T + 1) (Fin.snoc (α := fun _ => S) w x) = pathProb π P T w * P (w (Fin.last T)) x := by
                unfold pathProb
                rw [Fin.prod_univ_castSucc]
                have e0 : (Fin.snoc (α := fun _ => S) w x : Fin (T + 1 + 1) → S) 0 = w 0 := by
                  have := Fin.snoc_castSucc (α := fun _ => S) x w 0
                  simpa using this
                have e1 : ∀ i : Fin T, (Fin.snoc (α := fun _ => S) w x : Fin (T + 1 + 1) → S) (i.castSucc.succ) = w i.succ := by
                  intro i
                  rw [Fin.succ_castSucc]
                  exact Fin.snoc_castSucc (α := fun _ => S) x w _
                have e2 : (Fin.snoc (α := fun _ => S) w x : Fin (T + 1 + 1) → S) (Fin.last T).succ = x := by
                  rw [Fin.succ_last]
                  exact Fin.snoc_last (α := fun _ => S) x w
                have e3 : ∀ i : Fin (T + 1), (Fin.snoc (α := fun _ => S) w x : Fin (T + 1 + 1) → S) i.castSucc = w i := by
                  intro i
                  exact Fin.snoc_castSucc (α := fun _ => S) x w _
                rw [e0, e2, e3]
                simp only [e1, e3]
                ring
              change pathProb π P (T + 1) (Fin.snoc (α := fun _ => S) w x) * G (Fin.snoc (α := fun _ => S) w x) = _
              rw [h0]
              ring
            have trunc :
              ∀ (P : S → S → ℝ) (π : S → ℝ), IsStochastic P → ∀ (n k : ℕ) (F : (ℕ → S) → ℝ),
                (∀ w w' : ℕ → S, (∀ i ≤ n, w i = w' i) → F w = F w') →
                pathExp π P (n + k) (fun w => F (extendPath w)) = pathExp π P n (fun w => F (extendPath w)) := by
              intro P π hP n k F hF
              induction k with
              | zero => rfl
              | succ k ih =>
                rw [← ih]
                change pathExp π P (n + k + 1) _ = _
                rw [step]
                congr 1
                funext w
                have h : ∀ x, F (extendPath (Fin.snoc (α := fun _ => S) w x : Fin (n + k + 1 + 1) → S)) = F (extendPath w) := by
                  intro x
                  refine hF _ _ fun i hi => ?_
                  have h1 : min i (n + k + 1) = i := by omega
                  have h2 : min i (n + k) = i := by omega
                  have := Fin.snoc_castSucc (α := fun _ => S) x w ⟨i, by omega⟩
                  simp only [extendPath, h1, h2]
                  exact this
                simp only [h]
                rw [← Finset.sum_mul, hP.2, one_mul]
            have trunc2 :
              ∀ (P : S → S → ℝ) (π : S → ℝ), IsStochastic P → ∀ (n T : ℕ), n ≤ T → ∀ (F : (ℕ → S) → ℝ),
                (∀ w w' : ℕ → S, (∀ i ≤ n, w i = w' i) → F w = F w') →
                pathExp π P T (fun w => F (extendPath w)) = pathExp π P n (fun w => F (extendPath w)) := by
              intro P π hP n T h F hF
              obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
              exact trunc P π hP n k F hF
            have onestep :
              ∀ (P : S → S → ℝ) (π : S → ℝ), IsStochastic P → ∀ (n T : ℕ), n + 1 ≤ T → ∀ (F : (ℕ → S) → S → ℝ),
                (∀ w w' : ℕ → S, (∀ i ≤ n, w i = w' i) → F w = F w') →
                pathExp π P T (fun w => F (extendPath w) (extendPath w (n + 1))) =
                  pathExp π P T (fun w => ∑ u, P (extendPath w n) u * F (extendPath w) u) := by
              intro P π hP n T h F hF
              rw [trunc2 P π hP (n + 1) T h (fun w => F w (w (n + 1))) ?_,
                trunc2 P π hP n T (by omega) (fun w => ∑ u, P (w n) u * F w u) ?_, step]
              · congr 1
                funext w
                refine Finset.sum_congr rfl fun x _ => ?_
                have e1 : extendPath (Fin.snoc (α := fun _ => S) w x : Fin (n + 1 + 1) → S) (n + 1) = x := by
                  have := Fin.snoc_last (α := fun _ => S) x w
                  simp only [extendPath, min_self]
                  exact this
                have e2 : extendPath w n = w (Fin.last n) := by
                  simp only [extendPath, min_self]
                  rfl
                have e3 : F (extendPath (Fin.snoc (α := fun _ => S) w x : Fin (n + 1 + 1) → S)) = F (extendPath w) := by
                  refine hF _ _ fun i hi => ?_
                  have h1 : min i (n + 1) = i := by omega
                  have h2 : min i n = i := by omega
                  have := Fin.snoc_castSucc (α := fun _ => S) x w ⟨i, by omega⟩
                  simp only [extendPath, h1, h2]
                  exact this
                simp only [e1, e2, e3]
              · intro w w' hw
                simp only [hw n le_rfl, hF w w' hw]
              · intro w w' hw
                simp only [hw (n + 1) le_rfl, hF w w' (fun i hi => hw i (by omega))]
            have kstep :
              ∀ (P : S → S → ℝ) (π : S → ℝ), IsStochastic P → ∀ (n k T : ℕ), n + k ≤ T → ∀ (F : (ℕ → S) → S → ℝ),
                (∀ w w' : ℕ → S, (∀ i ≤ n, w i = w' i) → F w = F w') →
                pathExp π P T (fun w => F (extendPath w) (extendPath w (n + k))) =
                  pathExp π P T (fun w => ∑ u, (Matrix.of P ^ k) (extendPath w n) u * F (extendPath w) u) := by
              intro P π hP n k
              induction k with
              | zero =>
                intro T _ F _
                congr 1
                funext w
                simp [Matrix.one_apply]
              | succ k ih =>
                intro T hT F hF
                have h1 := onestep P π hP (n + k) T hT F (fun w w' h => hF w w' (fun i hi => h i (by omega)))
                have h2 := ih T (by omega) (fun w v => ∑ u, P v u * F w u) (fun w w' h => by simp only [hF w w' h])
                rw [show n + (k + 1) = n + k + 1 from rfl, h1, h2]
                congr 1
                funext w
                simp only [pow_succ, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, Matrix.of_apply]
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
            have e0 :
              ∀ (P : S → S → ℝ) (π : S → ℝ), IsStochastic P → ∀ (T : ℕ) (f : S → ℝ),
                pathExp π P T (fun w => f (extendPath w 0)) = ∑ s, π s * f s := by
              intro P π hP T f
              rw [trunc2 P π hP 0 T (by omega) (fun w => f (w 0)) (fun w w' h => by simp only [h 0 le_rfl])]
              unfold pathExp pathProb
              rw [← (Equiv.funUnique (Fin 1) S).symm.sum_comp]
              refine Finset.sum_congr rfl fun x _ => ?_
              simp [extendPath]
            have eone :
              ∀ (P : S → S → ℝ) (π : S → ℝ), IsStochastic P → IsStationaryDist P π → ∀ (T : ℕ) (c : ℝ),
                pathExp π P T (fun _ => c) = c := by
              intro P π hP hπ T c
              have := e0 P π hP T (fun _ => c)
              rw [this, ← Finset.sum_mul, hπ.2.1, one_mul]
            have emono :
              ∀ (P : S → S → ℝ) (π : S → ℝ), IsStochastic P → IsStationaryDist P π → ∀ (T : ℕ) (F G : (Fin (T + 1) → S) → ℝ),
                (∀ w, F w ≤ G w) → pathExp π P T F ≤ pathExp π P T G := by
              intro P π hP hπ T F G h
              unfold pathExp
              refine Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (h w) ?_
              exact mul_nonneg (hπ.1 _) (Finset.prod_nonneg fun i _ => hP.1 _ _)
            have eadd :
              ∀ (P : S → S → ℝ) (π : S → ℝ) (T : ℕ) (F G : (Fin (T + 1) → S) → ℝ),
                pathExp π P T (fun w => F w + G w) = pathExp π P T F + pathExp π P T G := by
              intro P π T F G
              simp only [pathExp, mul_add, Finset.sum_add_distrib]
            have emul :
              ∀ (P : S → S → ℝ) (π : S → ℝ) (T : ℕ) (c : ℝ) (F : (Fin (T + 1) → S) → ℝ),
                pathExp π P T (fun w => c * F w) = c * pathExp π P T F := by
              intro P π T c F
              simp only [pathExp, Finset.mul_sum]
              exact Finset.sum_congr rfl fun w _ => by ring
            have esum :
              ∀ (P : S → S → ℝ) (π : S → ℝ) (T n : ℕ) (F : ℕ → (Fin (T + 1) → S) → ℝ),
                pathExp π P T (fun w => ∑ k ∈ Finset.range n, F k w) = ∑ k ∈ Finset.range n, pathExp π P T (F k) := by
              intro P π T n F
              simp only [pathExp, Finset.mul_sum]
              rw [Finset.sum_comm]
            have Pk :
              ∀ (P : S → S → ℝ), IsStochastic P → ∀ k : ℕ, (∀ s u, 0 ≤ (Matrix.of P ^ k) s u) ∧ (∀ s, ∑ u, (Matrix.of P ^ k) s u = 1) := by
              intro P hP k
              induction k with
              | zero =>
                refine ⟨fun s u => ?_, fun s => ?_⟩
                · simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
                · simp [Matrix.one_apply]
              | succ k ih =>
                refine ⟨fun s u => ?_, fun s => ?_⟩
                · simp only [pow_succ, Matrix.mul_apply, Matrix.of_apply]
                  exact Finset.sum_nonneg fun v _ => mul_nonneg (ih.1 _ _) (hP.1 _ _)
                · simp only [pow_succ, Matrix.mul_apply, Matrix.of_apply]
                  rw [Finset.sum_comm]
                  simp only [← Finset.mul_sum, hP.2, mul_one, ih.2]
            have piPk :
              ∀ (P : S → S → ℝ) (π : S → ℝ), IsStationaryDist P π → ∀ (k : ℕ) (u : S), ∑ s, π s * (Matrix.of P ^ k) s u = π u := by
              intro P π hπ k
              induction k with
              | zero => intro u; simp [Matrix.one_apply]
              | succ k ih =>
                intro u
                simp only [pow_succ, Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum]
                rw [Finset.sum_comm]
                simp only [← mul_assoc, ← Finset.sum_mul, ih]
                exact hπ.2.2 u
            have Pkb :
              ∀ (P : S → S → ℝ), IsStochastic P → ∀ (k : ℕ) (f : S → ℝ) (B : ℝ), (∀ s, |f s| ≤ B) →
                ∀ s, |((Matrix.of P ^ k).mulVec f) s| ≤ B := by
              intro P hP k f B hf s
              simp only [Matrix.mulVec, dotProduct]
              calc _ ≤ ∑ u, |(Matrix.of P ^ k) s u * f u| := Finset.abs_sum_le_sum_abs _ _
                _ ≤ ∑ u, (Matrix.of P ^ k) s u * B := by
                  refine Finset.sum_le_sum fun u _ => ?_
                  rw [abs_mul, abs_of_nonneg ((Pk P hP k).1 s u)]
                  exact mul_le_mul_of_nonneg_left (hf u) ((Pk P hP k).1 s u)
                _ = B := by rw [← Finset.sum_mul, (Pk P hP k).2 s, one_mul]
            have Rsum :
              ∀ (P : S → S → ℝ), IsStochastic P → ∀ (q : ℝ), 0 ≤ q → q < 1 → ∀ (f : S → ℝ) (s : S),
                Summable (fun k : ℕ => q ^ k * ((Matrix.of P ^ k).mulVec f) s) := by
              intro P hP q hq0 hq1 f s
              have hf : ∀ u, |f u| ≤ ∑ v, |f v| := fun u => Finset.single_le_sum (f := fun v => |f v|) (fun v _ => abs_nonneg _) (Finset.mem_univ u)
              refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hq0 hq1).mul_right (∑ v, |f v|)) fun k => ?_
              rw [norm_mul, Real.norm_of_nonneg (pow_nonneg hq0 k), Real.norm_eq_abs]
              exact mul_le_mul_of_nonneg_left (Pkb P hP k f _ hf s) (pow_nonneg hq0 k)
            have Rtail :
              ∀ (P : S → S → ℝ), IsStochastic P → ∀ (q : ℝ), 0 ≤ q → q < 1 → ∀ (f : S → ℝ) (B : ℝ), (∀ s, |f s| ≤ B) →
                ∀ (n : ℕ) (s : S), |(∑' k : ℕ, q ^ k * ((Matrix.of P ^ k).mulVec f) s) -
                  ∑ k ∈ Finset.range n, q ^ k * ((Matrix.of P ^ k).mulVec f) s| ≤ q ^ n * (B / (1 - q)) := by
              intro P hP q hq0 hq1 f B hf n s
              rw [← (Rsum P hP q hq0 hq1 f s).sum_add_tsum_nat_add n, add_sub_cancel_left, ← Real.norm_eq_abs]
              have hg := ((hasSum_geometric_of_lt_one hq0 hq1).mul_left (q ^ n * B))
              rw [show q ^ n * (B / (1 - q)) = q ^ n * B * (1 - q)⁻¹ by rw [div_eq_mul_inv]; ring]
              refine tsum_of_norm_bounded hg fun k => ?_
              rw [norm_mul, Real.norm_of_nonneg (pow_nonneg hq0 _), Real.norm_eq_abs]
              calc _ ≤ q ^ (k + n) * B := mul_le_mul_of_nonneg_left (Pkb P hP _ f _ hf s) (pow_nonneg hq0 _)
                _ = _ := by rw [pow_add]; ring
            have Rbd :
              ∀ (P : S → S → ℝ), IsStochastic P → ∀ (q : ℝ), 0 ≤ q → q < 1 → ∀ (f : S → ℝ) (B : ℝ), (∀ s, |f s| ≤ B) →
                ∀ (s : S), |∑' k : ℕ, q ^ k * ((Matrix.of P ^ k).mulVec f) s| ≤ B / (1 - q) := by
              intro P hP q hq0 hq1 f B hf s
              have := Rtail P hP q hq0 hq1 f B hf 0 s
              simpa using this
            have Rsub :
              ∀ (P : S → S → ℝ), IsStochastic P → ∀ (q : ℝ), 0 ≤ q → q < 1 → ∀ (f g : S → ℝ) (c : ℝ) (s : S),
                (∑' k : ℕ, q ^ k * ((Matrix.of P ^ k).mulVec (f - c • g)) s) =
                (∑' k : ℕ, q ^ k * ((Matrix.of P ^ k).mulVec f) s) - c * ∑' k : ℕ, q ^ k * ((Matrix.of P ^ k).mulVec g) s := by
              intro P hP q hq0 hq1 f g c s
              rw [← tsum_mul_left, ← (Rsum P hP q hq0 hq1 f s).tsum_sub ((Rsum P hP q hq0 hq1 g s).mul_left c)]
              congr 1
              funext k
              rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
              simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
              ring
            have Rshift :
              ∀ (P : S → S → ℝ), IsStochastic P → ∀ (q : ℝ), 0 ≤ q → q < 1 → ∀ (f : S → ℝ) (s : S),
                (∑' k : ℕ, q ^ k * ((Matrix.of P ^ k).mulVec f) s) =
                f s + q * ∑' k : ℕ, q ^ k * ((Matrix.of P ^ k).mulVec ((Matrix.of P).mulVec f)) s := by
              intro P hP q hq0 hq1 f s
              rw [(Rsum P hP q hq0 hq1 f s).tsum_eq_zero_add, ← tsum_mul_left]
              congr 1
              · simp
              · congr 1
                funext k
                rw [Matrix.mulVec_mulVec, ← pow_succ, pow_succ q]
                ring
            have Rquad :
              ∀ (P : S → S → ℝ) (π : S → ℝ), IsStochastic P → IsStationaryDist P π → ∀ (k : ℕ) (v : S → ℝ),
                ∑ s, π s * v s * ((Matrix.of P ^ k).mulVec v) s ≤ ∑ s, π s * v s ^ 2 := by
              intro P π hP hπ k v
              simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
              calc _ ≤ ∑ s, ∑ u, ((1/2) * (π s * v s ^ 2 * (Matrix.of P ^ k) s u) + (1/2) * (π s * (Matrix.of P ^ k) s u * v u ^ 2)) := by
                    refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun u _ => ?_
                    have h := mul_nonneg (mul_nonneg (hπ.1 s) ((Pk P hP k).1 s u)) (sq_nonneg (v s - v u))
                    linarith only [h]
                _ = _ := by
                    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, (Pk P hP k).2, mul_one]
                    rw [Finset.sum_comm (f := fun s u => π s * (Matrix.of P ^ k) s u * v u ^ 2)]
                    simp only [← Finset.sum_mul, piPk P π hπ]
                    ring
            have Rquad2 :
              ∀ (P : S → S → ℝ) (π : S → ℝ), IsStochastic P → IsStationaryDist P π → ∀ (q : ℝ), 0 ≤ q → q < 1 → ∀ (v : S → ℝ),
                ∑ s, π s * v s * (∑' k : ℕ, q ^ k * ((Matrix.of P ^ k).mulVec ((Matrix.of P).mulVec v)) s)
                  ≤ (∑ s, π s * v s ^ 2) / (1 - q) := by
              intro P π hP hπ q hq0 hq1 v
              simp only [← tsum_mul_left]
              have hs : ∀ s ∈ Finset.univ, Summable (fun k : ℕ => π s * v s * (q ^ k * ((Matrix.of P ^ k).mulVec ((Matrix.of P).mulVec v)) s)) :=
                fun s _ => (Rsum P hP q hq0 hq1 _ s).mul_left _
              rw [← Summable.tsum_finsetSum hs, div_eq_mul_inv]
              have hg := ((hasSum_geometric_of_lt_one hq0 hq1).mul_left (∑ s, π s * v s ^ 2))
              refine (Summable.tsum_le_tsum (fun k => ?_) (summable_sum hs) hg.summable).trans_eq hg.tsum_eq
              have := mul_le_mul_of_nonneg_left (Rquad P π hP hπ (k + 1) v) (pow_nonneg hq0 k)
              rw [Finset.mul_sum] at this
              rw [mul_comm _ (q ^ k)]
              refine le_trans (le_of_eq ?_) this
              refine Finset.sum_congr rfl fun s _ => ?_
              rw [Matrix.mulVec_mulVec, ← pow_succ]
              ring
            have hq0 : 0 ≤ γ * lam := mul_nonneg hγ0 hlam0
            have hq1 : γ * lam < 1 := lt_of_le_of_lt (mul_le_of_le_one_right hγ0 hlam1) hγ1
            have hR0 : 0 ≤ R := (norm_nonneg _).trans hθ0
            obtain ⟨s0⟩ := ‹Nonempty S›
            have hr0 : 0 ≤ rmax := (abs_nonneg _).trans (hRw s0 s0)
            obtain ⟨D, hD⟩ : ∃ D : EuclideanSpace ℝ (Fin d) → S → ℝ, ∀ θ u, D θ u = ∑ u', P u u' * tdErr γ Rw φ θ u u' := ⟨_, fun _ _ => rfl⟩
            obtain ⟨RES, hRES⟩ : ∃ RES : (S → ℝ) → S → ℝ, ∀ f s, RES f s = ∑' k : ℕ, (γ * lam) ^ k * ((Matrix.of P ^ k).mulVec f) s := ⟨_, fun _ _ => rfl⟩
            obtain ⟨X, hX⟩ : ∃ X : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d), ∀ θ, X θ = xbar π P γ lam Rw φ θ := ⟨_, fun _ => rfl⟩
            have hin :
              ∀ (θ : EuclideanSpace ℝ (Fin d)) (s : S), |inner ℝ (φ s) θ| ≤ ‖θ‖ := by
              intro θ s
              calc |inner ℝ (φ s) θ| ≤ ‖φ s‖ * ‖θ‖ := abs_real_inner_le_norm _ _
                _ ≤ 1 * ‖θ‖ := mul_le_mul_of_nonneg_right (hφ s) (norm_nonneg _)
                _ = ‖θ‖ := one_mul _
            have htd :
              ∀ (θ : EuclideanSpace ℝ (Fin d)), ‖θ‖ ≤ R → ∀ s s', |tdErr γ Rw φ θ s s'| ≤ rmax + 2 * R := by
              intro θ hθ s s'
              have h1 := abs_le.mp (hRw s s')
              have h2 := abs_le.mp ((hin θ s).trans hθ)
              have h3 : |γ * inner ℝ (φ s') θ| ≤ R := by
                rw [abs_mul, abs_of_nonneg hγ0]
                exact (mul_le_of_le_one_left (abs_nonneg _) hγ1.le).trans ((hin θ s').trans hθ)
              have h3 := abs_le.mp h3
              unfold tdErr
              rw [abs_le]
              constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
            have htdsub :
              ∀ (θ θ' : EuclideanSpace ℝ (Fin d)) s s', |tdErr γ Rw φ θ s s' - tdErr γ Rw φ θ' s s'| ≤ 2 * ‖θ - θ'‖ := by
              intro θ θ' s s'
              have h2 := abs_le.mp (hin (θ - θ') s)
              have h3 : |γ * inner ℝ (φ s') (θ - θ')| ≤ ‖θ - θ'‖ := by
                rw [abs_mul, abs_of_nonneg hγ0]
                exact (mul_le_of_le_one_left (abs_nonneg _) hγ1.le).trans (hin (θ - θ') s')
              have h3 := abs_le.mp h3
              have e : tdErr γ Rw φ θ s s' - tdErr γ Rw φ θ' s s' = γ * inner ℝ (φ s') (θ - θ') - inner ℝ (φ s) (θ - θ') := by
                unfold tdErr
                rw [inner_sub_right, inner_sub_right]
                ring
              rw [e, abs_le]
              constructor <;> linarith only [h2.1, h2.2, h3.1, h3.2]
            have wavg :
              ∀ (p f : S → ℝ) (B : ℝ), (∀ s, 0 ≤ p s) → ∑ s, p s = 1 → (∀ s, |f s| ≤ B) → |∑ s, p s * f s| ≤ B := by
              intro p f B h0 h1 hf
              calc _ ≤ ∑ u, |p u * f u| := Finset.abs_sum_le_sum_abs _ _
                _ ≤ ∑ u, p u * B := by
                  refine Finset.sum_le_sum fun u _ => ?_
                  rw [abs_mul, abs_of_nonneg (h0 u)]
                  exact mul_le_mul_of_nonneg_left (hf u) (h0 u)
                _ = B := by rw [← Finset.sum_mul, h1, one_mul]
            have hDbd :
              ∀ (θ : EuclideanSpace ℝ (Fin d)), ‖θ‖ ≤ R → ∀ s, |D θ s| ≤ rmax + 2 * R := by
              intro θ hθ s
              rw [hD]
              exact wavg _ _ _ (hP.1 s) (hP.2 s) (htd θ hθ s)
            have hDsub :
              ∀ (θ θ' : EuclideanSpace ℝ (Fin d)), ∀ s, |(D θ - (1:ℝ) • D θ') s| ≤ 2 * ‖θ - θ'‖ := by
              intro θ θ' s
              have e : (D θ - (1:ℝ) • D θ') s = ∑ u, P s u * (tdErr γ Rw φ θ s u - tdErr γ Rw φ θ' s u) := by
                simp only [Pi.sub_apply, Pi.smul_apply, one_smul, hD, mul_sub, Finset.sum_sub_distrib]
              rw [e]
              exact wavg _ _ _ (hP.1 s) (hP.2 s) (htdsub θ θ' s)
            have X0 :
              ∀ (θ y : EuclideanSpace ℝ (Fin d)), inner ℝ (X θ) y = ∑ s, π s * (RES (D θ) s * inner ℝ (φ s) y) := by
              intro θ y
              have hDf : D θ = fun u => ∑ u', P u u' * (Rw u u' + γ * valFn φ θ u' - valFn φ θ u) := by
                funext u
                rw [hD]
                rfl
              rw [hX]
              unfold xbar gbarH
              rw [sum_inner]
              refine Finset.sum_congr rfl fun s _ => ?_
              rw [real_inner_smul_left]
              unfold Tlam
              rw [add_sub_cancel_left, hRES, hDf, mul_assoc]
            have X0n :
              ∀ (x : EuclideanSpace ℝ (Fin d)) (f : S → ℝ) (B : ℝ), 0 ≤ B → (∀ s, |f s| ≤ B) →
                (∀ y, inner ℝ x y = ∑ s, π s * (f s * inner ℝ (φ s) y)) → ‖x‖ ≤ B := by
              intro x f B hB hf hx
              have h := hx x
              rw [real_inner_self_eq_norm_sq] at h
              have h2 : |∑ s, π s * (f s * inner ℝ (φ s) x)| ≤ B * ‖x‖ := by
                refine wavg _ _ _ hπ.1 hπ.2.1 fun s => ?_
                rw [abs_mul]
                exact mul_le_mul (hf s) (hin x s) (abs_nonneg _) hB
              rw [← h, abs_of_nonneg (sq_nonneg _)] at h2
              rcases (norm_nonneg x).eq_or_lt with h0 | h0
              · rw [← h0]; exact hB
              · rw [pow_two] at h2
                exact le_of_mul_le_mul_right h2 h0
            have X1 :
              ∀ (θ : EuclideanSpace ℝ (Fin d)), ‖θ‖ ≤ R → ‖X θ‖ ≤ (rmax + 2 * R) / (1 - γ * lam) := by
              intro θ hθ
              refine X0n (X θ) (RES (D θ)) _ (div_nonneg (by linarith only [hr0, hR0]) (sub_pos.mpr hq1).le) (fun s => ?_) (X0 θ)
              rw [hRES]
              exact Rbd P hP _ hq0 hq1 _ _ (hDbd θ hθ) s
            have X2 :
              ∀ (θ θ' : EuclideanSpace ℝ (Fin d)), ‖X θ - X θ'‖ ≤ (2 * ‖θ - θ'‖) / (1 - γ * lam) := by
              intro θ θ'
              refine X0n (X θ - X θ') (RES (D θ - (1:ℝ) • D θ')) _ (div_nonneg (by positivity) (sub_pos.mpr hq1).le) (fun s => ?_) (fun y => ?_)
              · rw [hRES]
                exact Rbd P hP _ hq0 hq1 _ _ (hDsub θ θ') s
              · rw [inner_sub_left, X0, X0, ← Finset.sum_sub_distrib]
                refine Finset.sum_congr rfl fun s _ => ?_
                have := Rsub P hP _ hq0 hq1 (D θ) (D θ') 1 s
                rw [hRES, hRES, hRES, this]
                ring
            have X4 :
              ∀ (θ : EuclideanSpace ℝ (Fin d)), ‖θ‖ ≤ R → ∀ n : ℕ,
                |(∑ k ∈ Finset.range n, (γ * lam) ^ k * ∑ u, π u * (inner ℝ (φ u) (θ - θstar) * ((Matrix.of P ^ k).mulVec (D θ)) u))
                  - inner ℝ (X θ) (θ - θstar)| ≤ ((rmax + 2 * R) / (1 - γ * lam)) ^ 2 * (γ * lam) ^ n := by
              intro θ hθ n
              have e : (∑ k ∈ Finset.range n, (γ * lam) ^ k * ∑ u, π u * (inner ℝ (φ u) (θ - θstar) * ((Matrix.of P ^ k).mulVec (D θ)) u))
                  - inner ℝ (X θ) (θ - θstar) = ∑ u, π u * (inner ℝ (φ u) (θ - θstar) * -(RES (D θ) u - ∑ k ∈ Finset.range n, (γ * lam) ^ k * ((Matrix.of P ^ k).mulVec (D θ)) u)) := by
                rw [X0]
                simp only [Finset.mul_sum]
                rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
                refine Finset.sum_congr rfl fun u _ => ?_
                simp only [mul_neg, mul_sub, neg_sub, Finset.mul_sum]
                congr 1
                · exact Finset.sum_congr rfl fun k _ => by ring
                · ring
              rw [e]
              have hM : 0 ≤ rmax + 2 * R := by linarith only [hr0, hR0]
              have h1q : 0 < 1 - γ * lam := sub_pos.mpr hq1
              have hG : 0 ≤ (rmax + 2 * R) / (1 - γ * lam) := div_nonneg hM h1q.le
              have hMG : rmax + 2 * R ≤ (rmax + 2 * R) / (1 - γ * lam) := by
                rw [le_div_iff₀ h1q]
                exact mul_le_of_le_one_right hM (by linarith only [hq0])
              refine wavg _ _ _ hπ.1 hπ.2.1 fun u => ?_
              rw [abs_mul, abs_neg]
              have h1 : |inner ℝ (φ u) (θ - θstar)| ≤ (rmax + 2 * R) / (1 - γ * lam) := by
                have := hin (θ - θstar) u
                have h' := norm_sub_le θ θstar
                linarith only [this, h', hMG, hθ, hR, hr0]
              have h2 := Rtail P hP _ hq0 hq1 (D θ) _ (hDbd θ hθ) n u
              rw [← hRES] at h2
              calc _ ≤ (rmax + 2 * R) / (1 - γ * lam) * ((γ * lam) ^ n * ((rmax + 2 * R) / (1 - γ * lam))) :=
                    mul_le_mul h1 h2 (abs_nonneg _) hG
                _ = _ := by ring
            have Dscale :
              ∀ (a : ℝ) (x : EuclideanSpace ℝ (Fin d)), dNormSq π φ (a • x) = a ^ 2 * dNormSq π φ x := by
              intro a x
              simp only [dNormSq, inner_smul_right, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro s hs
              ring
            have Dom :
              ∀ (x : EuclideanSpace ℝ (Fin d)), ω * ‖x‖ ^ 2 ≤ dNormSq π φ x := by
              intro x
              by_cases hx : x = 0
              · subst hx
                simp [dNormSq]
              · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
                have hu : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
                  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
                have hl : ω ≤ dNormSq π φ ((‖x‖⁻¹ : ℝ) • x) := hω.2 ⟨_, hu, rfl⟩
                rw [Dscale, inv_pow] at hl
                have hp : 0 < ‖x‖ ^ 2 := by positivity
                rw [inv_mul_eq_div, le_div_iff₀ hp] at hl
                exact hl
            have Dle :
              ∀ (x : EuclideanSpace ℝ (Fin d)), dNormSq π φ x ≤ ‖x‖ ^ 2 := by
              intro x
              have := wavg π (fun s => inner ℝ (φ s) x ^ 2) (‖x‖ ^ 2) hπ.1 hπ.2.1 (fun s => by
                rw [abs_pow]
                exact pow_le_pow_left₀ (abs_nonneg _) (hin x s) 2)
              exact (le_abs_self _).trans this
            have om1 :
              ω ≤ 1 := by
              obtain ⟨⟨θ, h1, h2⟩, _⟩ := hω
              rw [h2]
              have := Dle θ
              rw [h1] at this
              simpa using this
            have hnormal :
              ∀ (v : S → ℝ) (y : EuclideanSpace ℝ (Fin d)),
                  ∑ s, π s * (projD π φ v s * inner ℝ (φ s) y) = ∑ s, π s * (v s * inner ℝ (φ s) y) := by
              have hact (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
                  (Matrix.mulVec (gram π φ) (fun j => x j)) i =
                    ∑ s, π s * valFn φ x s * φ s i := by
                simp only [gram, Matrix.mulVec, dotProduct, Matrix.of_apply, valFn,
                  PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
                simp only [Finset.sum_mul, Finset.mul_sum]
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro s hs
                apply Finset.sum_congr rfl
                intro j hj
                ring
              have hquad (x : EuclideanSpace ℝ (Fin d)) :
                  dotProduct (fun i => x i) (Matrix.mulVec (gram π φ) (fun i => x i)) = dNormSq π φ x := by
                simp_rw [dotProduct, hact, Finset.mul_sum]
                rw [Finset.sum_comm]
                unfold dNormSq
                apply Finset.sum_congr rfl
                intro s hs
                simp only [valFn, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
                simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i hi
                apply Finset.sum_congr rfl
                intro j hj
                ring
              have hunit : IsUnit (gram π φ) := by
                apply Matrix.mulVec_injective_iff_isUnit.mp
                intro x y hxy
                have hz : Matrix.mulVec (gram π φ) (x - y) = 0 := by
                  rw [Matrix.mulVec_sub, hxy, sub_self]
                have hq := hquad (WithLp.toLp 2 (x - y))
                have : dNormSq π φ (WithLp.toLp 2 (x - y)) = 0 := by
                  change dotProduct (x - y) (Matrix.mulVec (gram π φ) (x - y)) = _ at hq
                  rw [← hq, hz]
                  simp
                have he : WithLp.toLp 2 (x - y) = 0 := by
                  by_contra hn
                  have h1 := Dom (WithLp.toLp 2 (x - y))
                  have h2 : 0 < ‖(WithLp.toLp 2 (x - y) : EuclideanSpace ℝ (Fin d))‖ := norm_pos_iff.mpr hn
                  have h3 : 0 < ω * ‖(WithLp.toLp 2 (x - y) : EuclideanSpace ℝ (Fin d))‖ ^ 2 := by positivity
                  linarith only [h1, h3, this]
                have : x - y = 0 := by simpa using congrArg (WithLp.ofLp) he
                exact sub_eq_zero.mp this
              have hnormal (v : S → ℝ) (i : Fin d) :
                  ∑ s, π s * projD π φ v s * φ s i = ∑ s, π s * v s * φ s i := by
                have hn : Matrix.mulVec (gram π φ) (fun j => projCoef π φ v j) =
                    (fun j => ∑ s, π s * v s * φ s j) := by
                  change Matrix.mulVec (gram π φ)
                    (Matrix.mulVec (gram π φ)⁻¹ (fun j => ∑ s, π s * v s * φ s j)) = _
                  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
                    ((Matrix.isUnit_iff_isUnit_det _).mp hunit), Matrix.one_mulVec]
                change (∑ s, π s * valFn φ (projCoef π φ v) s * φ s i) = _
                rw [← hact (projCoef π φ v) i]
                exact congrFun hn i
              have hpair (x : EuclideanSpace ℝ (Fin d)) (v : S → ℝ) :
                  ∑ s, π s * (v s * inner ℝ (φ s) x) =
                    ∑ i, x i * (∑ s, π s * v s * φ s i) := by
                simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
                simp_rw [Finset.mul_sum]
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro i hi
                apply Finset.sum_congr rfl
                intro s hs
                ring
              intro v y
              rw [hpair, hpair]
              simp_rw [hnormal]
            have X3 :
              ∀ (θ : EuclideanSpace ℝ (Fin d)), (1 - kappa γ lam) * dNormSq π φ (θstar - θ) ≤ inner ℝ (θstar - θ) (X θ) := by
              intro θ
              have h1q : 0 < 1 - γ * lam := sub_pos.mpr hq1
              have hst : inner ℝ (X θstar) (θstar - θ) = 0 := by
                have h := hnormal (Tlam P γ lam Rw (valFn φ θstar)) (θstar - θ)
                rw [← hfix] at h
                rw [hX]
                unfold xbar gbarH
                rw [sum_inner]
                simp only [real_inner_smul_left, mul_sub, sub_mul, Finset.sum_sub_distrib]
                simp only [mul_assoc]
                rw [h, sub_self]
              obtain ⟨v, hv⟩ : ∃ v : S → ℝ, ∀ s, v s = inner ℝ (φ s) (θstar - θ) := ⟨_, fun _ => rfl⟩
              have hDD : D θ - (1:ℝ) • D θstar = v - γ • (Matrix.of P).mulVec v := by
                funext s
                simp only [Pi.sub_apply, Pi.smul_apply, one_smul, hD, Matrix.mulVec, dotProduct, Matrix.of_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
                have e : v s = ∑ u, P s u * v s := by rw [← Finset.sum_mul, hP.2, one_mul]
                rw [e, ← Finset.sum_sub_distrib]
                refine Finset.sum_congr rfl fun u _ => ?_
                simp only [hv, tdErr, inner_sub_right]
                ring
              have hkey : inner ℝ (X θ) (θstar - θ) = ∑ s, π s * v s ^ 2 - (γ - γ * lam) * ∑ s, π s * v s * RES ((Matrix.of P).mulVec v) s := by
                have : inner ℝ (X θ) (θstar - θ) = inner ℝ (X θ) (θstar - θ) - inner ℝ (X θstar) (θstar - θ) := by rw [hst, sub_zero]
                rw [this, X0, X0, ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
                refine Finset.sum_congr rfl fun s _ => ?_
                have h1 := Rsub P hP _ hq0 hq1 (D θ) (D θstar) 1 s
                have h2 := Rsub P hP _ hq0 hq1 v ((Matrix.of P).mulVec v) γ s
                have h3 := Rshift P hP _ hq0 hq1 v s
                rw [hDD, h2, h3] at h1
                simp only [← hRES] at h1
                rw [← hv]
                have : RES (D θ) s = RES (D θstar) s + (v s + γ * lam * RES ((Matrix.of P).mulVec v) s - γ * RES ((Matrix.of P).mulVec v) s) := by linarith only [h1]
                rw [this]
                ring
              have hq := Rquad2 P π hP hπ _ hq0 hq1 v
              simp only [← hRES] at hq
              have hdn : dNormSq π φ (θstar - θ) = ∑ s, π s * v s ^ 2 := by
                simp only [dNormSq, hv]
              rw [real_inner_comm, hkey, hdn]
              have hgl : 0 ≤ γ - γ * lam := sub_nonneg.mpr (mul_le_of_le_one_right hγ0 hlam1)
              have := mul_le_mul_of_nonneg_left hq hgl
              have e : (1 - kappa γ lam) * ∑ s, π s * v s ^ 2 = ∑ s, π s * v s ^ 2 - (γ - γ * lam) * ((∑ s, π s * v s ^ 2) / (1 - γ * lam)) := by
                unfold kappa
                rw [div_eq_mul_inv, div_eq_mul_inv]
                ring
              rw [e]
              linarith only [this]
            obtain ⟨G, hG⟩ : ∃ G : ℝ, G = (rmax + 2 * R) / (1 - γ * lam) := ⟨_, rfl⟩
            have h1q : 0 < 1 - γ * lam := sub_pos.mpr hq1
            have hM0 : 0 ≤ rmax + 2 * R := by linarith only [hr0, hR0]
            have hG0 : 0 ≤ G := by rw [hG]; exact div_nonneg hM0 h1q.le
            have hMG : rmax + 2 * R ≤ G := by rw [hG, le_div_iff₀ h1q]; exact mul_le_of_le_one_right hM0 (by linarith only [hq0])
            have h2RG : 2 * R ≤ G := by linarith only [hMG, hr0]
            obtain ⟨Z, hZ⟩ : ∃ Z : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → S → S → ℝ, ∀ θ z s s', Z θ z s s' = inner ℝ (tdErr γ Rw φ θ s s' • z - X θ) (θ - θstar) := ⟨_, fun _ _ _ _ => rfl⟩
            have ztr :
              ∀ (w : ℕ → S) (t : ℕ), ‖traceN φ (γ * lam) w t‖ ≤ 1 / (1 - γ * lam) := by
              intro w t
              have hgeo : HasSum (fun k : ℕ => (γ * lam) ^ k) (1 - γ * lam)⁻¹ :=
                hasSum_geometric_of_lt_one hq0 hq1
              unfold traceN
              rw [one_div]
              calc _ ≤ ∑ k ∈ Finset.range (t + 1), ‖(γ * lam) ^ k • φ (w (t - k))‖ := norm_sum_le _ _
                _ ≤ ∑ k ∈ Finset.range (t + 1), (γ * lam) ^ k := by
                  refine Finset.sum_le_sum fun k _ => ?_
                  rw [norm_smul, Real.norm_of_nonneg (pow_nonneg hq0 k)]
                  exact mul_le_of_le_one_right (pow_nonneg hq0 k) (hφ _)
                _ ≤ _ := sum_le_hasSum _ (fun k _ => pow_nonneg hq0 k) hgeo
            have dz :
              ∀ (θ : EuclideanSpace ℝ (Fin d)), ‖θ‖ ≤ R → ∀ (w : ℕ → S) (t : ℕ) s s', ‖tdErr γ Rw φ θ s s' • traceN φ (γ * lam) w t‖ ≤ G := by
              intro θ hθ w t s s'
              rw [norm_smul, Real.norm_eq_abs, hG, div_eq_mul_one_div]
              exact mul_le_mul (htd θ hθ s s') (ztr w t) (norm_nonneg _) hM0
            have projn :
              ∀ (θ : EuclideanSpace ℝ (Fin d)), ‖projBall R θ‖ ≤ R := by
              intro θ
              unfold projBall
              split_ifs with h
              · exact h
              · rw [not_le] at h
                have h0 : 0 < ‖θ‖ := lt_of_le_of_lt hR0 h
                rw [norm_smul, norm_div, norm_norm, Real.norm_of_nonneg hR0, div_mul_cancel₀ _ h0.ne']
            have projd :
              ∀ (θ y : EuclideanSpace ℝ (Fin d)), ‖y‖ ≤ R → ‖y - projBall R θ‖ ≤ ‖y - θ‖ := by
              intro θ y hy
              unfold projBall
              split_ifs with h
              · exact le_rfl
              · rw [not_le] at h
                have h0 : 0 < ‖θ‖ := lt_of_le_of_lt hR0 h
                have hi : inner ℝ y θ ≤ R * ‖θ‖ := (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hy h0.le)
                refine le_of_sq_le_sq ?_ (norm_nonneg _)
                rw [norm_sub_sq_real, norm_sub_sq_real, inner_smul_right, norm_smul, norm_div, norm_norm, Real.norm_of_nonneg hR0, div_mul_cancel₀ _ h0.ne']
                have e : inner ℝ y θ = (inner ℝ y θ / ‖θ‖) * ‖θ‖ := (div_mul_cancel₀ _ h0.ne').symm
                obtain ⟨c, hc⟩ : ∃ c, c = inner ℝ y θ / ‖θ‖ := ⟨_, rfl⟩
                have hcR : c ≤ R := by rw [hc, div_le_iff₀ h0]; exact hi
                have e2 : R / ‖θ‖ * inner ℝ y θ = R * c := by rw [hc]; ring
                rw [e2, e, ← hc]
                have h1 := mul_nonneg (by linarith only [h] : 0 ≤ ‖θ‖ - R) (by linarith only [h, hcR] : 0 ≤ ‖θ‖ + R - 2 * c)
                linarith only [h1]
            have thR :
              ∀ (α : ℕ → ℝ) (w : ℕ → S) (t : ℕ), ‖ptdLam γ lam Rw φ R α θ0 w t‖ ≤ R := by
              intro α w t
              cases t with
              | zero => exact hθ0
              | succ t => exact projn _
            have thstep :
              ∀ (α : ℕ → ℝ) (w : ℕ → S) (t : ℕ), 0 ≤ α t → ‖ptdLam γ lam Rw φ R α θ0 w (t + 1) - ptdLam γ lam Rw φ R α θ0 w t‖ ≤ G * α t := by
              intro α w t hα
              have h := projd (ptdLam γ lam Rw φ R α θ0 w t +
                    α t • (tdErr γ Rw φ (ptdLam γ lam Rw φ R α θ0 w t) (w t) (w (t + 1)) • traceN φ (γ * lam) w t)) (ptdLam γ lam Rw φ R α θ0 w t) (thR α w t)
              rw [sub_add_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg hα] at h
              rw [norm_sub_rev]
              refine le_trans h ?_
              rw [mul_comm]
              exact mul_le_mul_of_nonneg_right (dz _ (thR α w t) w t _ _) hα
            have thlag :
              ∀ (α : ℕ → ℝ) (w : ℕ → S) (b n : ℕ), (∀ i < b + n, 0 ≤ α i) → ‖ptdLam γ lam Rw φ R α θ0 w (b + n) - ptdLam γ lam Rw φ R α θ0 w b‖ ≤ G * ∑ i ∈ Finset.range n, α (b + i) := by
              intro α w b n
              induction n with
              | zero => intro _; simp
              | succ n ih =>
                intro hα
                have h1 := ih (fun i hi => hα i (by omega))
                have h2 := thstep α w (b + n) (hα _ (by omega))
                rw [Finset.sum_range_succ, mul_add]
                calc _ = ‖(ptdLam γ lam Rw φ R α θ0 w (b + n + 1) - ptdLam γ lam Rw φ R α θ0 w (b + n)) + (ptdLam γ lam Rw φ R α θ0 w (b + n) - ptdLam γ lam Rw φ R α θ0 w b)‖ := by
                      rw [sub_add_sub_cancel]; rfl
                  _ ≤ _ := (norm_add_le _ _).trans (by linarith only [h1, h2])
            have thdep :
              ∀ (α : ℕ → ℝ) (t : ℕ) (w w' : ℕ → S), (∀ i ≤ t, w i = w' i) → ptdLam γ lam Rw φ R α θ0 w t = ptdLam γ lam Rw φ R α θ0 w' t := by
              intro α t
              induction t with
              | zero => intro w w' _; rfl
              | succ t ih =>
                intro w w' h
                have h1 := ih w w' (fun i hi => h i (by omega))
                have h2 : traceN φ (γ * lam) w t = traceN φ (γ * lam) w' t := by
                  unfold traceN
                  refine Finset.sum_congr rfl fun k _ => ?_
                  rw [h (t - k) (by omega)]
                simp only [ptdLam]
                rw [h1, h2, h t (by omega), h (t + 1) le_rfl]
            have descent :
              ∀ (α : ℕ → ℝ) (w : ℕ → S) (t : ℕ), 0 ≤ α t →
                  ‖θstar - ptdLam γ lam Rw φ R α θ0 w (t + 1)‖ ^ 2 ≤
                    ‖θstar - ptdLam γ lam Rw φ R α θ0 w t‖ ^ 2
                      - 2 * α t * ((1 - kappa γ lam) * dNormSq π φ (θstar - ptdLam γ lam Rw φ R α θ0 w t))
                      + 2 * α t * Z (ptdLam γ lam Rw φ R α θ0 w t)
                          (traceN φ (γ * lam) w t) (w t) (w (t + 1))
                      + α t ^ 2 * G ^ 2 := by
              intro α w t hα
              have h := projd (ptdLam γ lam Rw φ R α θ0 w t +
                    α t • (tdErr γ Rw φ (ptdLam γ lam Rw φ R α θ0 w t) (w t) (w (t + 1)) • traceN φ (γ * lam) w t)) θstar hR
              have h2 := dz _ (thR α w t) w t (w t) (w (t + 1))
              have h3 := X3 (ptdLam γ lam Rw φ R α θ0 w t)
              rw [hZ]
              change ‖θstar - projBall R (ptdLam γ lam Rw φ R α θ0 w t +
                    α t • (tdErr γ Rw φ (ptdLam γ lam Rw φ R α θ0 w t) (w t) (w (t + 1)) • traceN φ (γ * lam) w t))‖ ^ 2 ≤ _
              generalize tdErr γ Rw φ (ptdLam γ lam Rw φ R α θ0 w t) (w t) (w (t + 1)) • traceN φ (γ * lam) w t = g at h h2 ⊢
              generalize ptdLam γ lam Rw φ R α θ0 w t = θ at h h3 ⊢
              have h4 := pow_le_pow_left₀ (norm_nonneg _) h 2
              have h5 : ‖θstar - (θ + α t • g)‖ ^ 2 = ‖θstar - θ‖ ^ 2 - 2 * α t * inner ℝ (θstar - θ) g + α t ^ 2 * ‖g‖ ^ 2 := by
                rw [← sub_sub, norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
                ring
              have h6 : inner ℝ (g - X θ) (θ - θstar) = inner ℝ (θstar - θ) (X θ) - inner ℝ (θstar - θ) g := by
                rw [real_inner_comm, ← neg_sub θstar θ, inner_neg_left, inner_sub_right]
                ring
              have h7 := pow_le_pow_left₀ (norm_nonneg _) h2 2
              have h8 := mul_le_mul_of_nonneg_left h7 (sq_nonneg (α t))
              have h9 := mul_le_mul_of_nonneg_left h3 (mul_nonneg zero_le_two hα)
              rw [h5] at h4
              rw [h6]
              linarith only [h4, h8, h9]
            have Zlip :
              ∀ (θ θ' : EuclideanSpace ℝ (Fin d)), ‖θ‖ ≤ R → ‖θ'‖ ≤ R → ∀ (w : ℕ → S) (t : ℕ) s s',
                Z θ (traceN φ (γ * lam) w t) s s' ≤ Z θ' (traceN φ (γ * lam) w t) s s' + 6 * G * ‖θ - θ'‖ := by
              intro θ θ' hθ hθ' w t s s'
              rw [hZ, hZ]
              have a1 := dz θ hθ w t s s'
              have a2 := X1 θ hθ
              rw [← hG] at a2
              have a3 := X2 θ θ'
              have a4 : ‖tdErr γ Rw φ θ s s' • traceN φ (γ * lam) w t - tdErr γ Rw φ θ' s s' • traceN φ (γ * lam) w t‖ ≤ (2 * ‖θ - θ'‖) / (1 - γ * lam) := by
                rw [← sub_smul, norm_smul, Real.norm_eq_abs, div_eq_mul_one_div]
                exact mul_le_mul (htdsub θ θ' s s') (ztr w t) (norm_nonneg _) (by positivity)
              generalize tdErr γ Rw φ θ s s' • traceN φ (γ * lam) w t = u at a1 a4 ⊢
              generalize tdErr γ Rw φ θ' s s' • traceN φ (γ * lam) w t = u' at a4 ⊢
              have e : inner ℝ (u - X θ) (θ - θstar) = inner ℝ (u' - X θ') (θ' - θstar) + (inner ℝ (u - X θ) (θ - θ') + inner ℝ ((u - u') - (X θ - X θ')) (θ' - θstar)) := by
                simp only [inner_sub_left, inner_sub_right]
                ring
              have b1 : inner ℝ (u - X θ) (θ - θ') ≤ 2 * G * ‖θ - θ'‖ := by
                refine (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
                exact (norm_sub_le _ _).trans (by linarith only [a1, a2])
              have b2 : inner ℝ ((u - u') - (X θ - X θ')) (θ' - θstar) ≤ (2 * ((2 * ‖θ - θ'‖) / (1 - γ * lam))) * (2 * R) := by
                refine (real_inner_le_norm _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity))
                · exact (norm_sub_le _ _).trans (by linarith only [a3, a4])
                · exact (norm_sub_le _ _).trans (by linarith only [hθ', hR])
              have b3 : (2 * ((2 * ‖θ - θ'‖) / (1 - γ * lam))) * (2 * R) ≤ 4 * G * ‖θ - θ'‖ := by
                have : (2 * ((2 * ‖θ - θ'‖) / (1 - γ * lam))) * (2 * R) = 4 * (2 * R / (1 - γ * lam)) * ‖θ - θ'‖ := by ring
                rw [this]
                refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
                rw [hG]
                have := div_le_div_of_nonneg_right (by linarith only [hr0] : 2 * R ≤ rmax + 2 * R) h1q.le
                linarith only [this]
              rw [e]
              linarith only [b1, b2, b3]
            have tau1 :
              ∀ (ε : ℝ), 0 < ε → m * ρ ^ tauMixLam m ρ (γ * lam) ε ≤ ε ∧ (γ * lam) ^ tauMixLam m ρ (γ * lam) ε ≤ ε := by
              intro ε hε
              obtain ⟨hm, hρ0, hρ1, _⟩ := hA1
              constructor
              · have hne : {t : ℕ | m * ρ ^ t ≤ ε}.Nonempty := by
                  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε hm) hρ1
                  refine ⟨n, ?_⟩
                  rw [lt_div_iff₀ hm] at hn
                  change m * ρ ^ n ≤ ε
                  linarith only [hn]
                have h1 : m * ρ ^ tauMix m ρ ε ≤ ε := Nat.sInf_mem hne
                refine le_trans (mul_le_mul_of_nonneg_left ?_ hm.le) h1
                exact pow_le_pow_of_le_one hρ0.le hρ1.le (le_max_left _ _)
              · have hne : {t : ℕ | (γ * lam) ^ t ≤ ε}.Nonempty := by
                  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hq1
                  exact ⟨n, hn.le⟩
                have h1 : (γ * lam) ^ tauAlgo (γ * lam) ε ≤ ε := Nat.sInf_mem hne
                exact le_trans (pow_le_pow_of_le_one hq0 hq1.le (le_max_right _ _)) h1
            have kap :
              0 < 1 - kappa γ lam ∧ 1 - kappa γ lam ≤ 1 := by
              have e : 1 - kappa γ lam = (1 - γ) / (1 - γ * lam) := by
                unfold kappa
                rw [eq_div_iff h1q.ne', sub_mul, div_mul_cancel₀ _ h1q.ne']
                ring
              rw [e]
              refine ⟨div_pos (sub_pos.mpr hγ1) h1q, ?_⟩
              rw [div_le_one h1q]
              exact sub_le_sub_left (mul_le_of_le_one_right hγ0 hlam1) 1
            have Zexp :
              ∀ (θ : EuclideanSpace ℝ (Fin d)) (w : ℕ → S) (t : ℕ) (s s' : S),
                Z θ (traceN φ (γ * lam) w t) s s' = (∑ k ∈ Finset.range (t + 1), (γ * lam) ^ k * (tdErr γ Rw φ θ s s' * inner ℝ (φ (w (t - k))) (θ - θstar))) - inner ℝ (X θ) (θ - θstar) := by
              intro θ w t s s'
              rw [hZ, inner_sub_left, real_inner_smul_left]
              unfold traceN
              rw [sum_inner, Finset.mul_sum]
              congr 1
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [real_inner_smul_left]
              ring
            have pair :
              ∀ (b j k T : ℕ), b + j + k + 1 ≤ T → ∀ Θ : (ℕ → S) → EuclideanSpace ℝ (Fin d), (∀ w w' : ℕ → S, (∀ i ≤ b, w i = w' i) → Θ w = Θ w') →
                pathExp π P T (fun w => tdErr γ Rw φ (Θ (extendPath w)) (extendPath w (b + j + k)) (extendPath w (b + j + k + 1)) * inner ℝ (φ (extendPath w (b + j))) (Θ (extendPath w) - θstar)) =
                pathExp π P T (fun w => ∑ u, (Matrix.of P ^ j) (extendPath w b) u * (inner ℝ (φ u) (Θ (extendPath w) - θstar) * ((Matrix.of P ^ k).mulVec (D (Θ (extendPath w)))) u)) := by
              intro b j k T hT Θ hΘ
              have h1 := onestep P π hP (b + j + k) T hT (fun w x => tdErr γ Rw φ (Θ w) (w (b + j + k)) x * inner ℝ (φ (w (b + j))) (Θ w - θstar)) (fun w w' h => by
                simp only [hΘ w w' (fun i hi => h i (by omega)), h (b + j + k) le_rfl, h (b + j) (by omega)])
              have h2 := kstep P π hP (b + j) k T (by omega) (fun w v => D (Θ w) v * inner ℝ (φ (w (b + j))) (Θ w - θstar)) (fun w w' h => by
                simp only [hΘ w w' (fun i hi => h i (by omega)), h (b + j) le_rfl])
              have h3 := kstep P π hP b j T (by omega) (fun w u => inner ℝ (φ u) (Θ w - θstar) * ((Matrix.of P ^ k).mulVec (D (Θ w))) u) (fun w w' h => by
                simp only [hΘ w w' h])
              rw [← h3]
              refine h1.trans (Eq.trans ?_ (h2.trans ?_))
              · congr 1
                funext w
                simp only [hD, Finset.sum_mul]
                exact Finset.sum_congr rfl fun u _ => by ring
              · congr 1
                funext w
                simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
                exact Finset.sum_congr rfl fun u _ => by ring
            have Zinit :
              ∀ (T t : ℕ), t + 1 ≤ T →
                pathExp π P T (fun w => Z θ0 (traceN φ (γ * lam) (extendPath w) t) (extendPath w t) (extendPath w (t + 1))) ≤ G ^ 2 * (γ * lam) ^ (t + 1) := by
              intro T t hT
              have h4 := (abs_le.mp (X4 θ0 hθ0 (t + 1))).2
              rw [← hG] at h4
              refine le_trans (le_of_eq ?_) h4
              simp only [Zexp, sub_eq_add_neg]
              rw [eadd, eone P π hP hπ, esum]
              congr 1
              refine Finset.sum_congr rfl fun k hk => ?_
              rw [emul]
              congr 1
              obtain ⟨j, hj⟩ : ∃ j, t = j + k := ⟨t - k, by have := Finset.mem_range.mp hk; omega⟩
              subst hj
              have hp := pair 0 j k T (by omega) (fun _ => θ0) (fun _ _ _ => rfl)
              simp only [Nat.zero_add] at hp
              simp only [Nat.add_sub_cancel, ← sub_eq_add_neg]
              rw [hp, e0 P π hP T (fun s => ∑ u, (Matrix.of P ^ j) s u * (inner ℝ (φ u) (θ0 - θstar) * ((Matrix.of P ^ k).mulVec (D θ0)) u))]
              simp only [Finset.mul_sum]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun u _ => ?_
              rw [← piPk P π hπ j u, Finset.sum_mul]
              exact Finset.sum_congr rfl fun s _ => by ring
            have ZA :
              ∀ (α : ℕ → ℝ) (T t : ℕ), (∀ i < t, 0 ≤ α i) → t + 1 ≤ T →
                pathExp π P T (fun w => Z (ptdLam γ lam Rw φ R α θ0 (extendPath w) t) (traceN φ (γ * lam) (extendPath w) t) (extendPath w t) (extendPath w (t + 1)))
                  ≤ 6 * G ^ 2 * ∑ i ∈ Finset.range t, α i + G ^ 2 * (γ * lam) ^ (t + 1) := by
              intro α T t hα hT
              have h1 := emono P π hP hπ T (fun w => Z (ptdLam γ lam Rw φ R α θ0 (extendPath w) t) (traceN φ (γ * lam) (extendPath w) t) (extendPath w t) (extendPath w (t + 1)))
                (fun w => Z θ0 (traceN φ (γ * lam) (extendPath w) t) (extendPath w t) (extendPath w (t + 1)) + 6 * G ^ 2 * ∑ i ∈ Finset.range t, α i) (fun w => by
                  have a1 := Zlip (ptdLam γ lam Rw φ R α θ0 (extendPath w) t) θ0 (thR _ _ _) hθ0 (extendPath w) t (extendPath w t) (extendPath w (t + 1))
                  have a2 := thlag α (extendPath w) 0 t (fun i hi => hα i (by omega))
                  simp only [Nat.zero_add] at a2
                  have a3 := mul_le_mul_of_nonneg_left a2 (mul_nonneg (by norm_num : (0:ℝ) ≤ 6) hG0)
                  have a4 : ptdLam γ lam Rw φ R α θ0 (extendPath w) 0 = θ0 := rfl
                  rw [a4] at a3
                  refine a1.trans ?_
                  linarith only [a3])
              rw [eadd, eone P π hP hπ] at h1
              have h2 := Zinit T t hT
              linarith only [h1, h2]
            have tv :
              ∀ (j τ : ℕ), τ ≤ j → ∀ (s : S) (h : S → ℝ) (B : ℝ), 0 ≤ B → (∀ u, |h u| ≤ B) →
                ∑ u, (Matrix.of P ^ j) s u * h u ≤ ∑ u, π u * h u + 2 * (m * ρ ^ τ) * B := by
              intro j τ hj s h B hB hh
              obtain ⟨hm, hρ0, hρ1, hA⟩ := hA1
              have h1 := hA j s
              unfold tvDist at h1
              have h2 : m * ρ ^ j ≤ m * ρ ^ τ := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ0.le hρ1.le hj) hm.le
              have h3 : ∑ u, (Matrix.of P ^ j) s u * h u - ∑ u, π u * h u ≤ (∑ u, |(Matrix.of P ^ j) s u - π u|) * B := by
                rw [← Finset.sum_sub_distrib, Finset.sum_mul]
                refine Finset.sum_le_sum fun u _ => ?_
                rw [← sub_mul]
                refine (le_abs_self _).trans ?_
                rw [abs_mul]
                exact mul_le_mul_of_nonneg_left (hh u) (abs_nonneg _)
              have h4 : (∑ u, |(Matrix.of P ^ j) s u - π u|) ≤ 2 * (m * ρ ^ τ) := by linarith only [h1, h2]
              have h5 := mul_le_mul_of_nonneg_right h4 hB
              linarith only [h3, h5]
            have Zlagged :
              ∀ (T b τ : ℕ), b + 2 * τ + 1 ≤ T → ∀ Θ : (ℕ → S) → EuclideanSpace ℝ (Fin d), (∀ w w' : ℕ → S, (∀ i ≤ b, w i = w' i) → Θ w = Θ w') → (∀ w, ‖Θ w‖ ≤ R) →
                pathExp π P T (fun w => Z (Θ (extendPath w)) (traceN φ (γ * lam) (extendPath w) (b + 2 * τ)) (extendPath w (b + 2 * τ)) (extendPath w (b + 2 * τ + 1)))
                  ≤ 2 * G ^ 2 * (γ * lam) ^ τ + 2 * G ^ 2 * (m * ρ ^ τ) := by
              intro T b τ hT Θ hΘ hΘR
              have hRM : 0 ≤ 2 * R * (rmax + 2 * R) := mul_nonneg (mul_nonneg zero_le_two hR0) hM0
              have hGE : 2 * R * (rmax + 2 * R) * (1 - γ * lam)⁻¹ ≤ G ^ 2 := by
                have : 2 * R * (rmax + 2 * R) * (1 - γ * lam)⁻¹ = 2 * R * G := by rw [hG]; ring
                rw [this, pow_two]
                exact mul_le_mul_of_nonneg_right h2RG hG0
              have hcb : ∀ (θ : EuclideanSpace ℝ (Fin d)) u, ‖θ‖ ≤ R → |inner ℝ (φ u) (θ - θstar)| ≤ 2 * R := by
                intro θ u hθ
                have h1 := hin (θ - θstar) u
                have h2 := norm_sub_le θ θstar
                linarith only [h1, h2, hθ, hR]
              have hgeo : HasSum (fun k : ℕ => (γ * lam) ^ k) (1 - γ * lam)⁻¹ :=
                hasSum_geometric_of_lt_one hq0 hq1
              have hmρ : 0 ≤ m * ρ ^ τ := mul_nonneg hA1.1.le (pow_nonneg hA1.2.1.le _)
              -- pointwise truncation
              have htrunc : ∀ w : ℕ → S, Z (Θ w) (traceN φ (γ * lam) w (b + 2 * τ)) (w (b + 2 * τ)) (w (b + 2 * τ + 1)) ≤
                  (∑ k ∈ Finset.range (τ + 1), (γ * lam) ^ k * (tdErr γ Rw φ (Θ w) (w (b + 2 * τ)) (w (b + 2 * τ + 1)) * inner ℝ (φ (w (b + 2 * τ - k))) (Θ w - θstar)))
                   + (G ^ 2 * (γ * lam) ^ τ - inner ℝ (X (Θ w)) (Θ w - θstar)) := by
                intro w
                rw [Zexp]
                have e : b + 2 * τ + 1 = (τ + 1) + (b + τ) := by omega
                rw [show Finset.range (b + 2 * τ + 1) = Finset.range ((τ + 1) + (b + τ)) by rw [e], Finset.sum_range_add]
                have hb : ∑ x ∈ Finset.range (b + τ), (γ * lam) ^ (τ + 1 + x) * (tdErr γ Rw φ (Θ w) (w (b + 2 * τ)) (w (b + 2 * τ + 1)) * inner ℝ (φ (w (b + 2 * τ - (τ + 1 + x)))) (Θ w - θstar)) ≤ G ^ 2 * (γ * lam) ^ τ := by
                  calc _ ≤ ∑ x ∈ Finset.range (b + τ), (γ * lam) ^ x * ((γ * lam) ^ τ * (2 * R * (rmax + 2 * R))) := by
                        refine Finset.sum_le_sum fun x _ => ?_
                        have a1 := htd (Θ w) (hΘR w) (w (b + 2 * τ)) (w (b + 2 * τ + 1))
                        have a2 := hcb (Θ w) (w (b + 2 * τ - (τ + 1 + x))) (hΘR w)
                        have a3 : tdErr γ Rw φ (Θ w) (w (b + 2 * τ)) (w (b + 2 * τ + 1)) * inner ℝ (φ (w (b + 2 * τ - (τ + 1 + x)))) (Θ w - θstar) ≤ 2 * R * (rmax + 2 * R) := by
                          refine (le_abs_self _).trans ?_
                          rw [abs_mul, mul_comm]
                          exact mul_le_mul a2 a1 (abs_nonneg _) (mul_nonneg zero_le_two hR0)
                        have a4 : (γ * lam) ^ (τ + 1 + x) ≤ (γ * lam) ^ x * (γ * lam) ^ τ := by
                          rw [← pow_add]
                          exact pow_le_pow_of_le_one hq0 hq1.le (by omega)
                        calc _ ≤ (γ * lam) ^ (τ + 1 + x) * (2 * R * (rmax + 2 * R)) := mul_le_mul_of_nonneg_left a3 (pow_nonneg hq0 _)
                          _ ≤ ((γ * lam) ^ x * (γ * lam) ^ τ) * (2 * R * (rmax + 2 * R)) := mul_le_mul_of_nonneg_right a4 hRM
                          _ = _ := by ring
                    _ = (∑ x ∈ Finset.range (b + τ), (γ * lam) ^ x) * ((γ * lam) ^ τ * (2 * R * (rmax + 2 * R))) := by rw [Finset.sum_mul]
                    _ ≤ (1 - γ * lam)⁻¹ * ((γ * lam) ^ τ * (2 * R * (rmax + 2 * R))) :=
                        mul_le_mul_of_nonneg_right (sum_le_hasSum _ (fun k _ => pow_nonneg hq0 k) hgeo) (mul_nonneg (pow_nonneg hq0 _) hRM)
                    _ = (2 * R * (rmax + 2 * R) * (1 - γ * lam)⁻¹) * (γ * lam) ^ τ := by ring
                    _ ≤ _ := mul_le_mul_of_nonneg_right hGE (pow_nonneg hq0 _)
                linarith only [hb]
              refine (emono P π hP hπ T _ _ (fun w => htrunc (extendPath w))).trans ?_
              rw [eadd, esum]
              have hterm : ∀ k ∈ Finset.range (τ + 1), pathExp π P T (fun w => (γ * lam) ^ k * (tdErr γ Rw φ (Θ (extendPath w)) (extendPath w (b + 2 * τ)) (extendPath w (b + 2 * τ + 1)) * inner ℝ (φ (extendPath w (b + 2 * τ - k))) (Θ (extendPath w) - θstar)))
                  ≤ pathExp π P T (fun w => (γ * lam) ^ k * (∑ u, π u * (inner ℝ (φ u) (Θ (extendPath w) - θstar) * ((Matrix.of P ^ k).mulVec (D (Θ (extendPath w)))) u) + 2 * (m * ρ ^ τ) * (2 * R * (rmax + 2 * R)))) := by
                intro k hk
                obtain ⟨j, hj, hjτ⟩ : ∃ j, 2 * τ = j + k ∧ τ ≤ j := ⟨2 * τ - k, by have := Finset.mem_range.mp hk; omega, by have := Finset.mem_range.mp hk; omega⟩
                rw [emul, emul]
                refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hq0 k)
                rw [hj, ← Nat.add_assoc, Nat.add_sub_cancel, pair b j k T (by omega) Θ hΘ]
                refine emono P π hP hπ T _ _ fun w => ?_
                refine tv j τ hjτ _ _ _ hRM fun u => ?_
                rw [abs_mul]
                exact mul_le_mul (hcb _ u (hΘR _)) (Pkb P hP k _ _ (hDbd _ (hΘR _)) u) (abs_nonneg _) (mul_nonneg zero_le_two hR0)
              refine (add_le_add_left (Finset.sum_le_sum hterm) _).trans ?_
              rw [← esum, ← eadd, ← eone P π hP hπ T (2 * G ^ 2 * (γ * lam) ^ τ + 2 * G ^ 2 * (m * ρ ^ τ))]
              refine emono P π hP hπ T _ _ fun w => ?_
              have h4 := (abs_le.mp (X4 (Θ (extendPath w)) (hΘR _) (τ + 1))).2
              rw [← hG] at h4
              have h5 : G ^ 2 * (γ * lam) ^ (τ + 1) ≤ G ^ 2 * (γ * lam) ^ τ := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq0 hq1.le (by omega)) (sq_nonneg G)
              have h6 : (∑ k ∈ Finset.range (τ + 1), (γ * lam) ^ k) * (2 * (m * ρ ^ τ) * (2 * R * (rmax + 2 * R))) ≤ 2 * G ^ 2 * (m * ρ ^ τ) := by
                calc _ ≤ (1 - γ * lam)⁻¹ * (2 * (m * ρ ^ τ) * (2 * R * (rmax + 2 * R))) :=
                      mul_le_mul_of_nonneg_right (sum_le_hasSum _ (fun k _ => pow_nonneg hq0 k) hgeo) (mul_nonneg (mul_nonneg zero_le_two hmρ) hRM)
                  _ = 2 * (m * ρ ^ τ) * (2 * R * (rmax + 2 * R) * (1 - γ * lam)⁻¹) := by ring
                  _ ≤ 2 * (m * ρ ^ τ) * G ^ 2 := mul_le_mul_of_nonneg_left hGE (mul_nonneg zero_le_two hmρ)
                  _ = _ := by ring
              have e : ∀ (A : ℕ → ℝ) (C : ℝ), ∑ k ∈ Finset.range (τ + 1), (γ * lam) ^ k * (A k + C) = ∑ k ∈ Finset.range (τ + 1), (γ * lam) ^ k * A k + (∑ k ∈ Finset.range (τ + 1), (γ * lam) ^ k) * C := by
                intro A C
                rw [Finset.sum_mul, ← Finset.sum_add_distrib]
                exact Finset.sum_congr rfl fun k _ => by ring
              rw [e (fun k => ∑ u, π u * (inner ℝ (φ u) (Θ (extendPath w) - θstar) * ((Matrix.of P ^ k).mulVec (D (Θ (extendPath w)))) u))]
              linarith only [h4, h5, h6]
            have ZB :
              ∀ (α : ℕ → ℝ) (T b τ : ℕ), (∀ i < b + 2 * τ, 0 ≤ α i) → b + 2 * τ + 1 ≤ T →
                pathExp π P T (fun w => Z (ptdLam γ lam Rw φ R α θ0 (extendPath w) (b + 2 * τ)) (traceN φ (γ * lam) (extendPath w) (b + 2 * τ)) (extendPath w (b + 2 * τ)) (extendPath w (b + 2 * τ + 1)))
                  ≤ 6 * G ^ 2 * ∑ i ∈ Finset.range (2 * τ), α (b + i) + (2 * G ^ 2 * (γ * lam) ^ τ + 2 * G ^ 2 * (m * ρ ^ τ)) := by
              intro α T b τ hα hT
              have h1 := emono P π hP hπ T (fun w => Z (ptdLam γ lam Rw φ R α θ0 (extendPath w) (b + 2 * τ)) (traceN φ (γ * lam) (extendPath w) (b + 2 * τ)) (extendPath w (b + 2 * τ)) (extendPath w (b + 2 * τ + 1)))
                (fun w => Z (ptdLam γ lam Rw φ R α θ0 (extendPath w) b) (traceN φ (γ * lam) (extendPath w) (b + 2 * τ)) (extendPath w (b + 2 * τ)) (extendPath w (b + 2 * τ + 1)) + 6 * G ^ 2 * ∑ i ∈ Finset.range (2 * τ), α (b + i)) (fun w => by
                  have a1 := Zlip (ptdLam γ lam Rw φ R α θ0 (extendPath w) (b + 2 * τ)) (ptdLam γ lam Rw φ R α θ0 (extendPath w) b) (thR _ _ _) (thR _ _ _) (extendPath w) (b + 2 * τ) (extendPath w (b + 2 * τ)) (extendPath w (b + 2 * τ + 1))
                  have a2 := thlag α (extendPath w) b (2 * τ) hα
                  have a3 := mul_le_mul_of_nonneg_left a2 (mul_nonneg (by norm_num : (0:ℝ) ≤ 6) hG0)
                  refine a1.trans ?_
                  linarith only [a3])
              rw [eadd, eone P π hP hπ] at h1
              have h2 := Zlagged T b τ hT (fun w => ptdLam γ lam Rw φ R α θ0 w b) (fun w w' h => thdep α b w w' h) (fun w => thR α w b)
              linarith only [h1, h2]
            obtain ⟨hk0, hk1⟩ := kap
            obtain ⟨y, hy⟩ : ∃ y : ℝ, y = ω * (1 - kappa γ lam) := ⟨_, rfl⟩
            have hy0 : 0 < y := by rw [hy]; exact mul_pos hω0 hk0
            have hy1 : y ≤ 1 := by rw [hy]; exact mul_le_one₀ om1 hk0.le hk1
            obtain ⟨EE, hEE⟩ : ∃ EE : (ℕ → ℝ) → ℕ → ℕ → ℝ, ∀ α T t, EE α T t = pathExp π P T (fun w => ‖θstar - ptdLam γ lam Rw φ R α θ0 (extendPath w) t‖ ^ 2) := ⟨_, fun _ _ _ => rfl⟩
            obtain ⟨DD, hDD⟩ : ∃ DD : (ℕ → ℝ) → ℕ → ℕ → ℝ, ∀ α T t, DD α T t = pathExp π P T (fun w => dNormSq π φ (θstar - ptdLam γ lam Rw φ R α θ0 (extendPath w) t)) := ⟨_, fun _ _ _ => rfl⟩
            obtain ⟨ZZ, hZZ⟩ : ∃ ZZ : (ℕ → ℝ) → ℕ → ℕ → ℝ, ∀ α T t, ZZ α T t = pathExp π P T (fun w => Z (ptdLam γ lam Rw φ R α θ0 (extendPath w) t) (traceN φ (γ * lam) (extendPath w) t) (extendPath w t) (extendPath w (t + 1))) := ⟨_, fun _ _ _ => rfl⟩
            clear step trunc trunc2 onestep kstep e0 Pk piPk Pkb Rsum Rtail Rbd Rsub Rshift Rquad Rquad2 hin htd htdsub wavg hDbd hDsub X0 X0n X1 X2 X4 Dscale Dle hnormal X3 ztr dz projn projd thR thstep thlag thdep Zlip Zexp pair Zinit tv Zlagged hfix hRw hD hRES hA1 hφ hlam0 hlam1 hγ0 hγ1 hr0 hR0 hR hθ0 hω h1q hM0 hMG h2RG om1
            have dE :
              ∀ (α : ℕ → ℝ) (T t : ℕ), 0 ≤ α t → EE α T (t + 1) ≤ EE α T t - 2 * α t * ((1 - kappa γ lam) * DD α T t) + 2 * α t * ZZ α T t + α t ^ 2 * G ^ 2 := by
              intro α T t hα
              rw [hEE, hEE, hDD, hZZ]
              have h := emono P π hP hπ T (fun w => ‖θstar - ptdLam γ lam Rw φ R α θ0 (extendPath w) (t + 1)‖ ^ 2)
                (fun w => ((‖θstar - ptdLam γ lam Rw φ R α θ0 (extendPath w) t‖ ^ 2
                  + (-(2 * α t * (1 - kappa γ lam))) * dNormSq π φ (θstar - ptdLam γ lam Rw φ R α θ0 (extendPath w) t))
                  + (2 * α t) * Z (ptdLam γ lam Rw φ R α θ0 (extendPath w) t) (traceN φ (γ * lam) (extendPath w) t) (extendPath w t) (extendPath w (t + 1)))
                  + α t ^ 2 * G ^ 2) (fun w => (descent α (extendPath w) t hα).trans (le_of_eq (by ring)))
              rw [eadd, eadd, eadd, emul, emul, eone P π hP hπ] at h
              linarith only [h]
            have DE :
              ∀ (α : ℕ → ℝ) (T t : ℕ), ω * EE α T t ≤ DD α T t := by
              intro α T t
              rw [hEE, hDD, ← emul]
              exact emono P π hP hπ T _ _ (fun w => Dom _)
            have EE0 :
              ∀ (α : ℕ → ℝ) (T : ℕ), EE α T 0 = ‖θstar - θ0‖ ^ 2 := by
              intro α T
              rw [hEE]
              exact eone P π hP hπ T (‖θstar - θ0‖ ^ 2)
            have EEnn :
              ∀ (α : ℕ → ℝ) (T t : ℕ), 0 ≤ EE α T t := by
              intro α T t
              rw [hEE, ← eone P π hP hπ T 0]
              exact emono P π hP hπ T _ _ (fun w => sq_nonneg _)
            have jens :
              ∀ (α : ℕ → ℝ) (T : ℕ), 1 ≤ T → pathExp π P T (fun w =>
                      dNormSq π φ (θstar - avgSeq (ptdLam γ lam Rw φ R α θ0 (extendPath w)) T)) ≤ (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, DD α T t := by
              intro α T hT
              simp only [hDD]
              rw [← esum, ← emul]
              refine emono P π hP hπ T _ _ fun w => ?_
              generalize ptdLam γ lam Rw φ R α θ0 (extendPath w) = th
              have hT0 : (0:ℝ) < T := by exact_mod_cast hT
              unfold dNormSq avgSeq
              rw [Finset.sum_comm, Finset.mul_sum]
              refine Finset.sum_le_sum fun s _ => ?_
              rw [← Finset.mul_sum, mul_left_comm]
              refine mul_le_mul_of_nonneg_left ?_ (hπ.1 s)
              have e : inner ℝ (φ s) (θstar - (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, th t) = (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, inner ℝ (φ s) (θstar - th t) := by
                simp only [inner_sub_right, inner_smul_right, inner_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
                rw [mul_sub, inv_mul_cancel_left₀ hT0.ne']
              rw [e, mul_pow]
              have h := sq_sum_le_card_mul_sum_sq (s := Finset.range T) (f := fun t => inner ℝ (φ s) (θstar - th t))
              rw [Finset.card_range] at h
              calc _ ≤ ((T : ℝ)⁻¹) ^ 2 * (T * ∑ t ∈ Finset.range T, inner ℝ (φ s) (θstar - th t) ^ 2) := mul_le_mul_of_nonneg_left h (sq_nonneg _)
                _ = _ := by rw [pow_two, mul_assoc, inv_mul_cancel_left₀ hT0.ne']
            have Zc :
              ∀ (a : ℝ) (α : ℕ → ℝ) (T : ℕ), 0 < a → (∀ t ≤ T, α t = a) → ∀ t, t + 1 ≤ T →
                (t < tauMixLam m ρ (γ * lam) a → ZZ α T t ≤ G ^ 2 * (6 * (tauMixLam m ρ (γ * lam) a : ℝ) * a + 1)) ∧
                (tauMixLam m ρ (γ * lam) a ≤ t → ZZ α T t ≤ G ^ 2 * ((6 + 12 * (tauMixLam m ρ (γ * lam) a : ℝ)) * a)) := by
              intro a α T ha hα t ht
              obtain ⟨t1, t2⟩ := tau1 a ha
              generalize tauMixLam m ρ (γ * lam) a = τ at t1 t2 ⊢
              have hG2 : 0 ≤ G ^ 2 := sq_nonneg G
              have hA := ZA α T t (fun i hi => by rw [hα i (by omega)]; exact ha.le) ht
              rw [← hZZ] at hA
              have hs : ∑ i ∈ Finset.range t, α i = t * a := by
                rw [Finset.sum_congr rfl (fun i hi => hα i (by have := Finset.mem_range.mp hi; omega)), Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              rw [hs] at hA
              refine ⟨fun h => ?_, fun h => ?_⟩
              · have hc : (t : ℝ) ≤ τ := by exact_mod_cast h.le
                have h1 : (t : ℝ) * a ≤ τ * a := mul_le_mul_of_nonneg_right hc ha.le
                have h2 : (γ * lam) ^ (t + 1) ≤ 1 := pow_le_one₀ hq0 hq1.le
                have h3 := mul_le_mul_of_nonneg_left h1 hG2
                have h4 := mul_le_mul_of_nonneg_left h2 hG2
                linarith only [hA, h3, h4]
              · by_cases h' : t < 2 * τ
                · have hc : (t : ℝ) ≤ 2 * τ := by exact_mod_cast h'.le
                  have h1 : (t : ℝ) * a ≤ 2 * τ * a := mul_le_mul_of_nonneg_right hc ha.le
                  have h2 : (γ * lam) ^ (t + 1) ≤ a := le_trans (pow_le_pow_of_le_one hq0 hq1.le (by omega)) t2
                  have h3 := mul_le_mul_of_nonneg_left h1 hG2
                  have h4 := mul_le_mul_of_nonneg_left h2 hG2
                  have h5 := mul_nonneg hG2 ha.le
                  linarith only [hA, h3, h4, h5]
                · obtain ⟨b, rfl⟩ : ∃ b, t = b + 2 * τ := ⟨t - 2 * τ, by omega⟩
                  have hB := ZB α T b τ (fun i hi => by rw [hα i (by omega)]; exact ha.le) ht
                  rw [← hZZ] at hB
                  have hs : ∑ i ∈ Finset.range (2 * τ), α (b + i) = (2 * τ : ℕ) * a := by
                    rw [Finset.sum_congr rfl (fun i hi => hα (b + i) (by have := Finset.mem_range.mp hi; omega)), Finset.sum_const, Finset.card_range, nsmul_eq_mul]
                  rw [hs] at hB
                  push_cast at hB
                  have h3 := mul_le_mul_of_nonneg_left t1 hG2
                  have h4 := mul_le_mul_of_nonneg_left t2 hG2
                  have h5 := mul_nonneg hG2 ha.le
                  linarith only [hB, h3, h4, h5]
            have partA :
              ∀ T : ℕ, 1 ≤ T → ∀ α : ℕ → ℝ, (∀ t ≤ T, α t = 1 / Real.sqrt T) →
                  pathExp π P T (fun w =>
                      dNormSq π φ (θstar - avgSeq (ptdLam γ lam Rw φ R α θ0 (extendPath w)) T)) ≤
                    (‖θstar - θ0‖ ^ 2 + G ^ 2
                        * (13 + 28 * (tauMixLam m ρ (γ * lam) (1 / Real.sqrt T) : ℝ)))
                      / (2 * Real.sqrt T * (1 - kappa γ lam)) := by
              intro T hT α hα
              refine (jens α T hT).trans ?_
              have hT0 : (1:ℝ) ≤ T := by exact_mod_cast hT
              have hs1 : 1 ≤ Real.sqrt T := Real.one_le_sqrt.mpr hT0
              have hsq : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt (Nat.cast_nonneg _)
              generalize Real.sqrt T = sT at hs1 hsq hα ⊢
              have hs0 : 0 < sT := lt_of_lt_of_le one_pos hs1
              obtain ⟨a, ha⟩ : ∃ a, a = 1 / sT := ⟨_, rfl⟩
              rw [← ha]
              rw [← ha] at hα
              have ha0 : 0 < a := by rw [ha]; exact one_div_pos.mpr hs0
              have ha1 : a ≤ 1 := by rw [ha, div_le_one hs0]; exact hs1
              have hZc := Zc a α T ha0 hα
              generalize tauMixLam m ρ (γ * lam) a = τ at hZc ⊢
              have hG2 : 0 ≤ G ^ 2 := sq_nonneg G
              have hind : ∀ n ≤ T, EE α T n + 2 * a * (1 - kappa γ lam) * ∑ t ∈ Finset.range n, DD α T t ≤ ‖θstar - θ0‖ ^ 2 + (n * (a ^ 2 * G ^ 2 * (13 + 24 * τ)) + (min n τ : ℕ) * (2 * a * G ^ 2)) := by
                intro n
                induction n with
                | zero => intro _; simp [EE0]
                | succ n ih =>
                  intro hn
                  have h1 := ih (by omega)
                  have h2 := dE α T n (by rw [hα n (by omega)]; exact ha0.le)
                  rw [hα n (by omega)] at h2
                  have hZ1 := hZc n hn
                  rw [Finset.sum_range_succ]
                  have h5 := mul_nonneg hG2 ha0.le
                  by_cases hc : n < τ
                  · have h3 := mul_le_mul_of_nonneg_left (hZ1.1 hc) (mul_nonneg zero_le_two ha0.le)
                    have e1 : min (n + 1) τ = n + 1 := by omega
                    have e2 : min n τ = n := by omega
                    rw [e1]
                    rw [e2] at h1
                    push_cast
                    have h6 : 0 ≤ a ^ 2 * G ^ 2 * (12 + 12 * (τ : ℝ)) := mul_nonneg (mul_nonneg (sq_nonneg a) hG2) (add_nonneg (by norm_num) (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
                    linarith only [h1, h2, h3, h6]
                  · have h3 := mul_le_mul_of_nonneg_left (hZ1.2 (by omega)) (mul_nonneg zero_le_two ha0.le)
                    have e1 : min (n + 1) τ = τ := by omega
                    have e2 : min n τ = τ := by omega
                    rw [e1]
                    rw [e2] at h1
                    push_cast
                    linarith only [h1, h2, h3]
              have h1 := hind T le_rfl
              have h2 := EEnn α T T
              have h3 : (min T τ : ℕ) * (2 * a * G ^ 2) ≤ (τ : ℝ) * (2 * a * G ^ 2) :=
                mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (min_le_right T τ)) (mul_nonneg (mul_nonneg zero_le_two ha0.le) hG2)
              have h4 : (τ : ℝ) * (2 * a * G ^ 2) ≤ (τ : ℝ) * (2 * G ^ 2) := by
                refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
                have := mul_le_mul_of_nonneg_right ha1 hG2
                linarith only [this]
              have hTa : (T : ℝ) * a ^ 2 = 1 := by
                rw [ha, ← hsq, one_div, inv_pow, pow_two]; exact mul_inv_cancel₀ (mul_pos hs0 hs0).ne'
              have h5 : (T : ℝ) * (a ^ 2 * G ^ 2 * (13 + 24 * τ)) = G ^ 2 * (13 + 24 * τ) := by
                calc _ = ((T : ℝ) * a ^ 2) * (G ^ 2 * (13 + 24 * τ)) := by ring
                  _ = _ := by rw [hTa, one_mul]
              rw [le_div_iff₀ (mul_pos (mul_pos two_pos hs0) hk0)]
              have e : (T : ℝ)⁻¹ * (∑ t ∈ Finset.range T, DD α T t) * (2 * sT * (1 - kappa γ lam)) = 2 * a * (1 - kappa γ lam) * ∑ t ∈ Finset.range T, DD α T t := by
                rw [ha, ← hsq, show (sT * sT)⁻¹ * (∑ t ∈ Finset.range T, DD α T t) * (2 * sT * (1 - kappa γ lam)) = (sT * sT⁻¹) * (2 * sT⁻¹ * (1 - kappa γ lam) * ∑ t ∈ Finset.range T, DD α T t) by rw [mul_inv]; ring, mul_inv_cancel₀ hs0.ne', one_mul, one_div]
              rw [e]
              have h6 : 0 ≤ (τ : ℝ) * G ^ 2 := mul_nonneg (Nat.cast_nonneg _) hG2
              linarith only [h1, h2, h3, h4, h5, h6]
            have partB :
              ∀ α0 : ℝ, 0 < α0 → α0 < 1 / (2 * ω * (1 - kappa γ lam)) →
                  ∀ T : ℕ, 2 * tauMixLam m ρ (γ * lam) α0 < T → ∀ α : ℕ → ℝ, (∀ t ≤ T, α t = α0) →
                  pathExp π P T (fun w => ‖θstar - ptdLam γ lam Rw φ R α θ0 (extendPath w) T‖ ^ 2) ≤
                    Real.exp (-2 * α0 * (1 - kappa γ lam) * ω * T) * ‖θstar - θ0‖ ^ 2
                      + α0 * (G ^ 2
                          * (13 + 24 * (tauMixLam m ρ (γ * lam) α0 : ℝ)) / (2 * (1 - kappa γ lam) * ω)) := by
              intro a ha0 ha T hT α hα
              rw [← hEE]
              have hZc := Zc a α T ha0 hα
              generalize tauMixLam m ρ (γ * lam) a = τ at hZc hT ⊢
              have hG2 : 0 ≤ G ^ 2 := sq_nonneg G
              rw [show 2 * ω * (1 - kappa γ lam) = 2 * y by rw [hy]; ring, lt_div_iff₀ (mul_pos two_pos hy0)] at ha
              rw [show -2 * a * (1 - kappa γ lam) * ω * T = T * (-(2 * a * y)) by rw [hy]; ring]
              obtain ⟨r, hr⟩ : ∃ r, r = 1 - 2 * a * y := ⟨_, rfl⟩
              have hay : 0 < a * y := mul_pos ha0 hy0
              have hr0 : 0 ≤ r := by rw [hr]; linarith only [ha]
              have hr1 : r ≤ 1 := by rw [hr]; linarith only [hay]
              have hrec : ∀ t, t + 1 ≤ T → EE α T (t + 1) ≤ r * EE α T t + a ^ 2 * G ^ 2 + 2 * a * ZZ α T t := by
                intro t ht
                have h2 := dE α T t (by rw [hα t (by omega)]; exact ha0.le)
                rw [hα t (by omega)] at h2
                have h3 := mul_le_mul_of_nonneg_left (DE α T t) (mul_nonneg (mul_nonneg zero_le_two ha0.le) hk0.le)
                rw [hr, hy]
                linarith only [h2, h3]
              obtain ⟨E0, hE0⟩ : ∃ E0, E0 = ‖θstar - θ0‖ ^ 2 := ⟨_, rfl⟩
              rw [← hE0]
              have hE0n : 0 ≤ E0 := by rw [hE0]; exact sq_nonneg _
              obtain ⟨k, hk⟩ : ∃ k, k = 1 / (2 * y) := ⟨_, rfl⟩
              have hky : 2 * y * k = 1 := by rw [hk]; exact mul_one_div_cancel (mul_pos two_pos hy0).ne'
              have hk2 : 1 / 2 ≤ k := by
                rw [hk]
                exact one_div_le_one_div_of_le (mul_pos two_pos hy0) (by linarith only [hy1])
              obtain ⟨A, hA⟩ : ∃ A, A = k * (a * G ^ 2 * (1 + 12 * (τ:ℝ))) := ⟨_, rfl⟩
              obtain ⟨C, hC⟩ : ∃ C, C = k * (a * G ^ 2 * (13 + 24 * (τ:ℝ))) := ⟨_, rfl⟩
              have hCe : a * (G ^ 2 * (13 + 24 * (τ:ℝ)) / (2 * (1 - kappa γ lam) * ω)) = C := by
                rw [hC, hk, hy, show 2 * (1 - kappa γ lam) * ω = 2 * (ω * (1 - kappa γ lam)) by ring]; ring
              rw [hCe]
              have hmul : ∀ N : ℝ, (1 - r) * (k * N) = a * N := by
                intro N
                rw [hr, show (1 - (1 - 2 * a * y)) * (k * N) = a * N * (2 * y * k) by ring, hky, mul_one]
              have hA1' : (1 - r) * A = a ^ 2 * G ^ 2 * (1 + 12 * (τ:ℝ)) := by
                rw [hA, hmul]; ring
              have hC1 : (1 - r) * C = a ^ 2 * G ^ 2 * (13 + 24 * (τ:ℝ)) := by
                rw [hC, hmul]; ring
              have hAC : A + τ * (2 * a * G ^ 2) ≤ C := by
                have h1 : 0 ≤ a * G ^ 2 := mul_nonneg ha0.le hG2
                have h2 : 0 ≤ (τ:ℝ) * (a * G ^ 2) := mul_nonneg (Nat.cast_nonneg _) h1
                have h3 := mul_le_mul_of_nonneg_right hk2 (by linarith only [h1, h2] : 0 ≤ 12 * (a * G ^ 2) + 12 * (τ * (a * G ^ 2)))
                rw [hA, hC]
                linarith only [h1, h2, h3]
              have hp1 : ∀ t ≤ τ, EE α T t ≤ r ^ t * E0 + (A + t * (2 * a * G ^ 2)) := by
                intro t
                induction t with
                | zero =>
                  intro _
                  rw [EE0, ← hE0]
                  have : 0 ≤ A := by
                    rw [hA]
                    exact mul_nonneg (by linarith only [hk2]) (mul_nonneg (mul_nonneg ha0.le hG2) (add_nonneg zero_le_one (mul_nonneg (by norm_num) (Nat.cast_nonneg _))))
                  simp only [pow_zero, one_mul, Nat.cast_zero, zero_mul, add_zero]
                  linarith only [this]
                | succ t ih =>
                  intro ht
                  have h1 := mul_le_mul_of_nonneg_left (ih (by omega)) hr0
                  have h2 := hrec t (by omega)
                  have h3 := mul_le_mul_of_nonneg_left ((hZc t (by omega)).1 (by omega)) (mul_nonneg zero_le_two ha0.le)
                  have h4 : r * (t * (2 * a * G ^ 2)) ≤ 1 * (t * (2 * a * G ^ 2)) := mul_le_mul_of_nonneg_right hr1 (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg zero_le_two ha0.le) hG2))
                  rw [pow_succ]
                  push_cast
                  linarith only [h1, h2, h3, h4, hA1']
              have hp2 : ∀ n, τ + n ≤ T → EE α T (τ + n) ≤ r ^ (τ + n) * E0 + C := by
                intro n
                induction n with
                | zero =>
                  intro _
                  have := hp1 τ le_rfl
                  simp only [Nat.add_zero]
                  linarith only [this, hAC]
                | succ n ih =>
                  intro ht
                  have h1 := mul_le_mul_of_nonneg_left (ih (by omega)) hr0
                  have h2 := hrec (τ + n) (by omega)
                  have h3 := mul_le_mul_of_nonneg_left ((hZc (τ + n) (by omega)).2 (by omega)) (mul_nonneg zero_le_two ha0.le)
                  rw [← Nat.add_assoc, pow_succ]
                  linarith only [h1, h2, h3, hC1]
              obtain ⟨n, hn⟩ : ∃ n, T = τ + n := ⟨T - τ, by omega⟩
              have h1 := hp2 n (by omega)
              rw [← hn] at h1
              have h2 : r ^ T ≤ Real.exp (T * (-(2 * a * y))) := by
                rw [Real.exp_nat_mul]
                refine pow_le_pow_left₀ hr0 ?_ T
                have := Real.add_one_le_exp (-(2 * a * y))
                rw [hr]
                linarith only [this]
              have h3 := mul_le_mul_of_nonneg_right h2 hE0n
              linarith only [h1, h3]
            have partC :
              ∀ T : ℕ, 1 ≤ T → ∀ α : ℕ → ℝ,
                  (∀ t : ℕ, α t = 1 / (ω * ((t : ℝ) + 1) * (1 - kappa γ lam))) →
                  pathExp π P T (fun w =>
                      dNormSq π φ (θstar - avgSeq (ptdLam γ lam Rw φ R α θ0 (extendPath w)) T)) ≤
                    G ^ 2
                        * (13 + 52 * (tauMixLam m ρ (γ * lam) (α T) : ℝ)) / (T * (1 - kappa γ lam) ^ 2 * ω)
                      * (1 + Real.log T) := by
              intro T hT α hα
              refine (jens α T hT).trans ?_
              have hT0 : (1:ℝ) ≤ T := by exact_mod_cast hT
              have hα' : ∀ t : ℕ, α t = 1 / y * (1 / ((t:ℝ) + 1)) := by
                intro t
                rw [hα, hy, ← one_div_mul_one_div_rev, ← one_div_mul_one_div_rev, ← one_div_mul_one_div_rev]
                ring
              have hαpos : ∀ t, 0 < α t := by
                intro t; rw [hα']; exact mul_pos (one_div_pos.mpr hy0) (one_div_pos.mpr (Nat.cast_add_one_pos t))
              have hαm : ∀ i ≤ T, α T ≤ α i := by
                intro i hi
                rw [hα', hα']
                have : (i:ℝ) ≤ T := by exact_mod_cast hi
                exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (Nat.cast_add_one_pos i) (by linarith only [this])) (one_div_pos.mpr hy0).le
              have hG2 : 0 ≤ G ^ 2 := sq_nonneg G
              obtain ⟨t1, t2⟩ := tau1 (α T) (hαpos T)
              generalize tauMixLam m ρ (γ * lam) (α T) = τ at t1 t2 ⊢
              obtain ⟨L, hL⟩ : ∃ L, L = 1 + Real.log T := ⟨_, rfl⟩
              rw [← hL]
              have hL1 : 1 ≤ L := by
                rw [hL]
                have := Real.log_nonneg hT0
                linarith only [this]
              have hLy : 1 ≤ L / y := by rw [le_div_iff₀ hy0]; linarith only [hy1, hL1]
              have hsum : ∀ n ≤ T, ∑ i ∈ Finset.range n, α i ≤ L / y := by
                intro n hn
                have h1 : ∑ i ∈ Finset.range n, α i ≤ ∑ i ∈ Finset.range T, α i :=
                  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn) (fun i _ _ => (hαpos i).le)
                refine h1.trans ?_
                have h2 := harmonic_le_one_add_log T
                have h3 : ((harmonic T : ℚ) : ℝ) = ∑ i ∈ Finset.range T, 1 / ((i:ℝ) + 1) := by
                  unfold harmonic
                  push_cast
                  exact Finset.sum_congr rfl fun i _ => by rw [one_div]
                rw [h3, ← hL] at h2
                simp only [hα']
                rw [← Finset.mul_sum, div_eq_mul_one_div L, mul_comm L]
                exact mul_le_mul_of_nonneg_left h2 (one_div_pos.mpr hy0).le
              have hsumnn : ∀ n, 0 ≤ ∑ i ∈ Finset.range n, α i := fun n => Finset.sum_nonneg fun i _ => (hαpos i).le
              have hind : ∀ n ≤ T, y * n * EE α T n + (1 - kappa γ lam) * ∑ t ∈ Finset.range n, DD α T t ≤ 2 * ∑ t ∈ Finset.range n, ZZ α T t + G ^ 2 * ∑ t ∈ Finset.range n, α t := by
                intro n
                induction n with
                | zero => intro _; simp
                | succ n ih =>
                  intro hn
                  have h1 := ih (by omega)
                  have h2 := dE α T n (hαpos n).le
                  have h3 := mul_le_mul_of_nonneg_left (DE α T n) (mul_nonneg (hαpos n).le hk0.le)
                  obtain ⟨β, hβ⟩ : ∃ β, β = y * ((n:ℝ) + 1) := ⟨_, rfl⟩
                  have hβ0 : 0 < β := by rw [hβ]; exact mul_pos hy0 (Nat.cast_add_one_pos n)
                  have hab : β * α n = 1 := by
                    have hn1 : (0:ℝ) < (n:ℝ) + 1 := Nat.cast_add_one_pos n
                    rw [hβ, hα', mul_mul_mul_comm, mul_one_div_cancel hy0.ne', mul_one_div_cancel hn1.ne', mul_one]
                  have h4 : EE α T (n + 1) ≤ EE α T n - α n * y * EE α T n - α n * ((1 - kappa γ lam) * DD α T n) + α n * (2 * ZZ α T n) + α n * (α n * G ^ 2) := by
                    rw [hy]
                    linarith only [h2, h3]
                  have h5 := mul_le_mul_of_nonneg_left h4 hβ0.le
                  have h6 : β * (EE α T n - α n * y * EE α T n - α n * ((1 - kappa γ lam) * DD α T n) + α n * (2 * ZZ α T n) + α n * (α n * G ^ 2)) = β * EE α T n - (β * α n) * (y * EE α T n) - (β * α n) * ((1 - kappa γ lam) * DD α T n) + (β * α n) * (2 * ZZ α T n) + (β * α n) * (α n * G ^ 2) := by ring
                  rw [h6, hab, hβ] at h5
                  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
                  push_cast
                  linarith only [h1, h5]
              have hZe : ∀ t, t + 1 ≤ T → ZZ α T t ≤ G ^ 2 * (6 * (L / y) + 1) := by
                intro t ht
                have hA := ZA α T t (fun i _ => (hαpos i).le) ht
                rw [← hZZ] at hA
                have h1 := mul_le_mul_of_nonneg_left (hsum t (by omega)) hG2
                have h2 := mul_le_mul_of_nonneg_left (pow_le_one₀ hq0 hq1.le : (γ * lam) ^ (t + 1) ≤ 1) hG2
                linarith only [hA, h1, h2]
              have hZl : ∀ b, b + 2 * τ + 1 ≤ T → ZZ α T (b + 2 * τ) ≤ G ^ 2 * (12 * τ + 4) * α b := by
                intro b hb
                have hB := ZB α T b τ (fun i _ => (hαpos i).le) hb
                rw [← hZZ] at hB
                have hs : ∑ i ∈ Finset.range (2 * τ), α (b + i) ≤ (2 * τ : ℕ) * α b := by
                  rw [← nsmul_eq_mul]
                  have := Finset.sum_le_card_nsmul (Finset.range (2 * τ)) (fun i => α (b + i)) (α b) (fun i _ => by
                    simp only [hα']
                    push_cast
                    have : (0:ℝ) ≤ i := Nat.cast_nonneg _
                    exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (Nat.cast_add_one_pos b) (by linarith only [this])) (one_div_pos.mpr hy0).le)
                  rwa [Finset.card_range] at this
                push_cast at hs
                have h1 := mul_le_mul_of_nonneg_left hs hG2
                have h2 := mul_le_mul_of_nonneg_left (t1.trans (hαm b (by omega))) hG2
                have h3 := mul_le_mul_of_nonneg_left (t2.trans (hαm b (by omega))) hG2
                linarith only [hB, h1, h2, h3]
              have hZs : ∑ t ∈ Finset.range T, ZZ α T t ≤ 2 * τ * (G ^ 2 * (6 * (L / y) + 1)) + G ^ 2 * (12 * τ + 4) * (L / y) := by
                have hc0 : 0 ≤ G ^ 2 * (6 * (L / y) + 1) := mul_nonneg hG2 (by linarith only [hLy])
                have hc1 : 0 ≤ G ^ 2 * (12 * (τ:ℝ) + 4) := mul_nonneg hG2 (add_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (by norm_num))
                by_cases hc : T ≤ 2 * τ
                · have h1 := Finset.sum_le_card_nsmul (Finset.range T) (fun t => ZZ α T t) (G ^ 2 * (6 * (L / y) + 1)) (fun i hi => hZe i (by have := Finset.mem_range.mp hi; omega))
                  rw [Finset.card_range, nsmul_eq_mul] at h1
                  have h2 : (T:ℝ) ≤ 2 * τ := by exact_mod_cast hc
                  have h3 := mul_le_mul_of_nonneg_right h2 hc0
                  have h4 : 0 ≤ G ^ 2 * (12 * (τ:ℝ) + 4) * (L / y) := mul_nonneg hc1 (by linarith only [hLy])
                  linarith only [h1, h3, h4]
                · obtain ⟨n, hn⟩ : ∃ n, T = 2 * τ + n := ⟨T - 2 * τ, by omega⟩
                  have e : ∑ t ∈ Finset.range T, ZZ α T t = ∑ t ∈ Finset.range (2 * τ), ZZ α T t + ∑ x ∈ Finset.range n, ZZ α T (2 * τ + x) := by
                    rw [← Finset.sum_range_add, ← hn]
                  rw [e]
                  have h1 := Finset.sum_le_card_nsmul (Finset.range (2 * τ)) (fun t => ZZ α T t) (G ^ 2 * (6 * (L / y) + 1)) (fun i hi => hZe i (by have := Finset.mem_range.mp hi; omega))
                  rw [Finset.card_range, nsmul_eq_mul] at h1
                  push_cast at h1
                  have h2 : ∑ x ∈ Finset.range n, ZZ α T (2 * τ + x) ≤ ∑ x ∈ Finset.range n, G ^ 2 * (12 * τ + 4) * α x := by
                    refine Finset.sum_le_sum fun x hx => ?_
                    have := Finset.mem_range.mp hx
                    rw [Nat.add_comm]
                    exact hZl x (by omega)
                  rw [← Finset.mul_sum] at h2
                  have h3 := mul_le_mul_of_nonneg_left (hsum n (by omega)) hc1
                  linarith only [h1, h2, h3]
              have h1 := hind T le_rfl
              have h2 : 0 ≤ y * T * EE α T T := mul_nonneg (mul_nonneg hy0.le (Nat.cast_nonneg _)) (EEnn α T T)
              have h3 := mul_le_mul_of_nonneg_left (hsum T le_rfl) hG2
              have h4 : (1 - kappa γ lam) * ∑ t ∈ Finset.range T, DD α T t ≤ G ^ 2 * (13 + 52 * τ) * (L / y) := by
                have h5 : (τ:ℝ) * G ^ 2 * 1 ≤ τ * G ^ 2 * (L / y) := mul_le_mul_of_nonneg_left hLy (mul_nonneg (Nat.cast_nonneg _) hG2)
                have h6 : 0 ≤ G ^ 2 * (L / y) := mul_nonneg hG2 (by linarith only [hLy])
                linarith only [h1, h2, h3, hZs, h5, h6]
              have e : G ^ 2 * (13 + 52 * (τ:ℝ)) / (T * (1 - kappa γ lam) ^ 2 * ω) * L = (T:ℝ)⁻¹ * (G ^ 2 * (13 + 52 * τ) * (L / y) / (1 - kappa γ lam)) := by
                rw [hy]
                simp only [div_eq_mul_inv, mul_inv, pow_two]
                ring
              rw [e]
              refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Nat.cast_nonneg _))
              rw [le_div_iff₀ hk0]
              linarith only [h4]
            rw [← hG]
            exact ⟨partA, partB, partC⟩
