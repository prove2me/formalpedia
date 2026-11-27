-- Prove2me | solution 1 for CrossLearnCB.UCB1CL.Supplement.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:09:44.143336+00:00
-- url     : https://prove2.me/submissions/46cbf86e-af86-48a0-bbe6-0751cc50797c

import Mathlib
import Definitions.Def_CrossLearnCB_UCB1CL_Supplement_AcyclicNumber
import Definitions.Def_CrossLearnCB_UCB1CL_Supplement_Protocol
import Definitions.Def_CrossLearnCB_UCB1CL_Supplement_Algorithms

open CrossLearnCB
open CrossLearnCB.UCB1CL
open CrossLearnCB.UCB1CL.Supplement

/-- Theorem 3, p. 24: there is an absolute constant `C₀` such that, when every arm has the same
CL graph `G`, EXP3.CL-U (Algorithm 3), which does not know the context distribution `D`, has
expected ex ante regret at most `C₀ λ(G) K^{1/3} T^{2/3} (log K)^{1/3}` against every oblivious
reward table with values in `[0, 1]`, whenever its probabilities are well defined
(`K log K ≤ T`, i.e. `Kα ≤ 1`). -/
theorem solution : ∃ C₀ : ℝ, ∀ (K C T : ℕ) [NeZero K] (G : Fin C → Fin C → Prop),
    (∀ c, G c c) → ∀ D : Fin C → ℝ, IsDistribution D →
    (K : ℝ) * Real.log K ≤ T →
    ∀ r : Fin T → Fin K → Fin C → ℝ, (∀ t i c, r t i c ∈ Set.Icc (0 : ℝ) 1) →
      exAnteRegret (fun _ : Fin K => G) D (exp3CLU T G) r
        ≤ C₀ * (maxAcyclicNumber G : ℝ) * (K : ℝ) ^ (1 / 3 : ℝ) * (T : ℝ) ^ (2 / 3 : ℝ)
          * Real.log K ^ (1 / 3 : ℝ) := by
            classical
            have lem1 : ∀ (C : ℕ) (G : Fin C → Fin C → Prop), (∀ c, G c c) → ∀ D : Fin C → ℝ,
                (∀ c, 0 ≤ D c) →
                ∑ c, D c / (∑ c', if G c' c then D c' else 0) ≤ (maxAcyclicNumber G : ℝ) := by
              intro C G hG D hD
              have ind : ∀ n : ℕ, ∀ S : Finset (Fin C), S.card ≤ n → ∃ (m : ℕ) (v : Fin m → Fin C),
                  (∀ i, v i ∈ S) ∧ (∀ i j : Fin m, j < i → ¬ G (v i) (v j)) ∧
                  ∑ c ∈ S, D c / (∑ c' ∈ S, if G c' c then D c' else 0) ≤ (m : ℝ) := by
                intro n
                induction n with
                | zero =>
                  intro S hS
                  have : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hS)
                  subst this
                  exact ⟨0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simp⟩
                | succ n ih =>
                  intro S hS
                  rcases S.eq_empty_or_nonempty with rfl | hne
                  · exact ⟨0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simp⟩
                  obtain ⟨a, haS, hmin⟩ := Finset.exists_min_image S
                    (fun c => ∑ c' ∈ S, if G c' c then D c' else 0) hne
                  have hcard : (S.filter (fun c => ¬ G c a)).card ≤ n := by
                    have : (S.filter (fun c => ¬ G c a)).card < S.card := by
                      apply Finset.card_lt_card
                      refine Finset.filter_ssubset.mpr ⟨a, haS, by simpa using hG a⟩
                    omega
                  obtain ⟨m, v, hvS, hvG, hsum⟩ := ih _ hcard
                  refine ⟨m + 1, Fin.cons a v, ?_, ?_, ?_⟩
                  · intro i
                    refine Fin.cases ?_ (fun i => ?_) i
                    · simpa using haS
                    · simpa using (Finset.mem_filter.mp (hvS i)).1
                  · intro i j
                    refine Fin.cases ?_ (fun i => ?_) i
                    · intro h; exact absurd h (by simp)
                    · refine Fin.cases ?_ (fun j => ?_) j
                      · intro _
                        simpa using (Finset.mem_filter.mp (hvS i)).2
                      · intro h
                        simpa using hvG i j (by simpa using h)
                  · rw [← Finset.sum_filter_add_sum_filter_not S (fun c => G c a)]
                    have hnn : ∀ c, 0 ≤ ∑ c' ∈ S, (if G c' c then D c' else 0) := by
                      intro c
                      refine Finset.sum_nonneg (fun c' _ => ?_)
                      split_ifs
                      · exact hD _
                      · exact le_rfl
                    have h1 : ∑ c ∈ S.filter (fun c => G c a),
                        D c / (∑ c' ∈ S, if G c' c then D c' else 0) ≤ 1 := by
                      rcases (hnn a).eq_or_lt with h0 | hpos
                      · have hz : ∀ c ∈ S.filter (fun c => G c a), D c = 0 := by
                          intro c hc
                          rw [← Finset.sum_filter] at h0
                          exact (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => hD c)).mp h0.symm c hc
                        rw [Finset.sum_eq_zero]
                        · norm_num
                        · intro c hc; rw [hz c hc]; simp
                      · calc _ ≤ ∑ c ∈ S.filter (fun c => G c a),
                            D c / (∑ c' ∈ S, if G c' a then D c' else 0) := by
                              refine Finset.sum_le_sum (fun c hc => ?_)
                              exact div_le_div_of_nonneg_left (hD c) hpos
                                (hmin c (Finset.mem_filter.mp hc).1)
                          _ = 1 := by
                              rw [← Finset.sum_div, Finset.sum_filter]
                              exact div_self hpos.ne'
                    have h2 : ∑ c ∈ S.filter (fun c => ¬ G c a),
                        D c / (∑ c' ∈ S, if G c' c then D c' else 0) ≤ (m : ℝ) := by
                      refine le_trans (Finset.sum_le_sum (fun c hc => ?_)) hsum
                      have hle : D c ≤ ∑ c' ∈ S.filter (fun c => ¬ G c a), if G c' c then D c' else 0 := by
                        have := Finset.single_le_sum (f := fun c' => if G c' c then D c' else 0)
                          (s := S.filter (fun c => ¬ G c a))
                          (fun c' _ => by split_ifs; exacts [hD _, le_rfl]) hc
                        simpa [hG c] using this
                      rcases (hD c).eq_or_lt with h0 | hpos
                      · rw [← h0]; simp
                      · refine div_le_div_of_nonneg_left (hD c) (lt_of_lt_of_le hpos hle) ?_
                        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
                        intro c' _ _
                        split_ifs
                        · exact hD _
                        · exact le_rfl
                    push_cast
                    linarith
              obtain ⟨m, v, -, hvG, hsum⟩ := ind _ Finset.univ le_rfl
              refine hsum.trans ?_
              have hinj : Function.Injective v := by
                intro i j hij
                rcases lt_trichotomy i j with h | h | h
                · exact absurd (hij ▸ hG (v i)) (hvG j i h)
                · exact h
                · exact absurd (hij ▸ hG (v i)) (hvG i j h)
              have : m ≤ maxAcyclicNumber G := by
                refine le_csSup ⟨Fintype.card (Fin C), ?_⟩ ⟨v, hinj, hvG⟩
                rintro r ⟨v, hv, -⟩
                simpa using Fintype.card_le_of_injective v hv
              exact_mod_cast this
            have key : ∀ (Ω : Type) [Fintype Ω] (q : (n : ℕ) → (Fin n → Ω) → Ω → ℝ)
                (Φ : (n : ℕ) → (Fin n → Ω) → ℝ) (b : ℝ),
                (∀ n τ ω, 0 ≤ q n τ ω) → (∀ n τ, ∑ ω, q n τ ω = 1) →
                (∀ n τ, ∑ ω, q n τ ω * Φ (n+1) (Fin.snoc (α := fun _ => Ω) τ ω) ≤ Φ n τ + b) → ∀ n : ℕ,
                (∑ τ : Fin n → Ω, ∏ t : Fin n, q t (fun s => τ (Fin.castLE t.2.le s)) (τ t)) = 1 ∧
                ∑ τ : Fin n → Ω, (∏ t : Fin n, q t (fun s => τ (Fin.castLE t.2.le s)) (τ t)) * Φ n τ
                  ≤ Φ 0 Fin.elim0 + n * b := by
              intro Ω _ q Φ b hq0 hq1 hd
              have step : ∀ (n : ℕ) (F : (Fin (n+1) → Ω) → ℝ),
                  ∑ τ : Fin (n+1) → Ω, (∏ t : Fin (n+1), q t (fun s => τ (Fin.castLE t.2.le s)) (τ t)) * F τ
                  = ∑ τ : Fin n → Ω, (∏ t : Fin n, q t (fun s => τ (Fin.castLE t.2.le s)) (τ t)) *
                    ∑ ω, q n τ ω * F (Fin.snoc (α := fun _ => Ω) τ ω) := by
                intro n F
                rw [← (Fin.snocEquiv (fun _ : Fin (n+1) => Ω)).sum_comp, Fintype.sum_prod_type,
                  Finset.sum_comm]
                refine Finset.sum_congr rfl (fun τ _ => ?_)
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl (fun ω _ => ?_)
                rw [← mul_assoc]
                congr 1
                rw [Fin.prod_univ_castSucc]
                congr 1
                · refine Finset.prod_congr rfl (fun t _ => ?_)
                  have e1 : (Fin.snocEquiv (fun _ : Fin (n+1) => Ω)) (ω, τ) (Fin.castSucc t) = τ t := by
                    simp [Fin.snocEquiv]
                  rw [e1]
                  have e2 : (fun s : Fin t => (Fin.snocEquiv (fun _ : Fin (n+1) => Ω)) (ω, τ)
                      (Fin.castLE (Fin.castSucc t).2.le s)) = fun s : Fin t => τ (Fin.castLE t.2.le s) := by
                    funext s
                    have : Fin.castLE (Fin.castSucc t).2.le s = Fin.castSucc (Fin.castLE t.2.le s) := rfl
                    rw [this]
                    exact Fin.snoc_castSucc (α := fun _ => Ω) ω τ _
                  exact congrFun (congrArg (q t) e2) _
                · have e1 : (Fin.snocEquiv (fun _ : Fin (n+1) => Ω)) (ω, τ) (Fin.last n) = ω := by
                    simp [Fin.snocEquiv]
                  rw [e1]
                  have e2 : (fun s : Fin n => (Fin.snocEquiv (fun _ : Fin (n+1) => Ω)) (ω, τ)
                      (Fin.castLE (Fin.last n).2.le s)) = τ := by
                    funext s
                    have : Fin.castLE (Fin.last n).2.le s = Fin.castSucc s := rfl
                    rw [this]
                    exact Fin.snoc_castSucc (α := fun _ => Ω) ω τ _
                  exact congrFun (congrArg (q n) e2) _
              have hP0 : ∀ (n : ℕ) (τ : Fin n → Ω),
                  0 ≤ ∏ t : Fin n, q t (fun s => τ (Fin.castLE t.2.le s)) (τ t) :=
                fun n τ => Finset.prod_nonneg (fun t _ => hq0 _ _ _)
              have h1 : ∀ n : ℕ,
                (∑ τ : Fin n → Ω, ∏ t : Fin n, q t (fun s => τ (Fin.castLE t.2.le s)) (τ t)) = 1 := by
                intro n
                induction n with
                | zero => simp
                | succ n ih =>
                  have := step n (fun _ => 1)
                  simp only [mul_one] at this
                  rw [this, ← ih]
                  refine Finset.sum_congr rfl (fun τ _ => ?_)
                  rw [hq1, mul_one]
              intro n
              refine ⟨h1 n, ?_⟩
              induction n with
              | zero => 
                simp
                exact le_of_eq (congrArg (Φ 0) (Subsingleton.elim _ _))
              | succ n ih =>
                rw [step]
                calc _ ≤ ∑ τ : Fin n → Ω, (∏ t : Fin n, q t (fun s => τ (Fin.castLE t.2.le s)) (τ t)) *
                      (Φ n τ + b) :=
                      Finset.sum_le_sum (fun τ _ => mul_le_mul_of_nonneg_left (hd n τ) (hP0 n τ))
                  _ = ∑ τ : Fin n → Ω, (∏ t : Fin n, q t (fun s => τ (Fin.castLE t.2.le s)) (τ t)) * Φ n τ
                      + b := by
                      simp only [mul_add, Finset.sum_add_distrib]
                      rw [← Finset.sum_mul, h1 n, one_mul]
                  _ ≤ _ := by push_cast; linarith
            have num : ∀ K T : ℝ, 1 < K → K * Real.log K ≤ T → ∀ α β A : ℝ,
                α = (Real.log K / (K ^ 2 * T)) ^ (1 / 3 : ℝ) → β = Real.sqrt (α * Real.log K / T) →
                A = K ^ (1 / 3 : ℝ) * T ^ (2 / 3 : ℝ) * Real.log K ^ (1 / 3 : ℝ) →
                0 < α ∧ 0 < β ∧ 0 ≤ A ∧ β ≤ α ∧ K * α ≤ 1 ∧ Real.log K / β = A ∧
                  T * (K * α + β / α) = 2 * A := by
              intro K T hK hT α β A hα hβ hA
              have hL : 0 < Real.log K := Real.log_pos hK
              generalize Real.log K = L at *
              have hK0 : 0 < K := by linarith
              have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
              have hα0 : 0 < α := by rw [hα]; positivity
              have hβ0 : 0 < β := by rw [hβ]; positivity
              have hA0 : 0 < A := by rw [hA]; positivity
              have third : ∀ x : ℝ, 0 ≤ x → (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
                intro x hx
                rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num
              have twothird : ∀ x : ℝ, 0 ≤ x → (x ^ (2 / 3 : ℝ)) ^ 3 = x ^ 2 := by
                intro x hx
                rw [← Real.rpow_natCast, ← Real.rpow_mul hx, ← Real.rpow_natCast]; norm_num
              have hα3 : α ^ 3 = L / (K ^ 2 * T) := by rw [hα]; exact third _ (by positivity)
              have hA3 : A ^ 3 = K * T ^ 2 * L := by
                rw [hA, mul_pow, mul_pow, third _ hK0.le, third _ hL.le, twothird _ hT0.le]
              have hβ2 : β ^ 2 = α * L / T := by rw [hβ]; exact Real.sq_sqrt (by positivity)
              have hAα : α * K * T = A := by
                refine (pow_left_inj₀ (by positivity) hA0.le (three_ne_zero)).mp ?_
                rw [hA3, mul_pow, mul_pow, hα3]; field_simp
              have hA2α : A ^ 2 * α = L * T := by
                rw [← hAα]
                have : (α * K * T) ^ 2 * α = α ^ 3 * (K ^ 2 * T ^ 2) := by ring
                rw [this, hα3]; field_simp
              have hLβ : L / β = A := by
                refine (pow_left_inj₀ (by positivity) hA0.le (two_ne_zero)).mp ?_
                rw [div_pow, hβ2, div_eq_iff (by positivity)]
                have : A ^ 2 * (α * L / T) = (A ^ 2 * α) * L / T := by ring
                rw [this, hA2α]; field_simp
              have hTβ : T * β / α = A := by
                refine (pow_left_inj₀ (by positivity) hA0.le (two_ne_zero)).mp ?_
                rw [div_pow, mul_pow, hβ2, div_eq_iff (by positivity)]
                have : A ^ 2 * α ^ 2 = (A ^ 2 * α) * α := by ring
                rw [this, hA2α]; field_simp
              have hAK : K * L ≤ A := by
                refine (pow_le_pow_iff_left₀ (by positivity) hA0.le (three_ne_zero)).mp ?_
                rw [hA3]
                have : (K * L) ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ (by positivity) hT 2
                calc (K * L) ^ 3 = (K * L) * (K * L) ^ 2 := by ring
                  _ ≤ (K * L) * T ^ 2 := by gcongr
                  _ = _ := by ring
              refine ⟨hα0, hβ0, hA0.le, ?_, ?_, hLβ, ?_⟩
              · have h1 : L ≤ α * T := by
                  rw [← hAα] at hAK
                  nlinarith
                refine (pow_le_pow_iff_left₀ hβ0.le hα0.le (two_ne_zero)).mp ?_
                rw [hβ2, div_le_iff₀ hT0]
                nlinarith
              · refine (pow_le_pow_iff_left₀ (by positivity) zero_le_one (three_ne_zero)).mp ?_
                rw [mul_pow, hα3, one_pow]
                rw [← mul_div_assoc, div_le_one (by positivity)]
                have := mul_le_mul_of_nonneg_left hT (sq_nonneg K)
                nlinarith
              · have : T * (K * α + β / α) = α * K * T + T * β / α := by ring
                rw [this, hAα, hTβ]; ring
            have drift : ∀ (K C : ℕ) (G : Fin C → Fin C → Prop) (D : Fin C → ℝ) (α β : ℝ)
                (w ρ : Fin K → Fin C → ℝ) (a : Fin C → Fin K) (S : ℝ),
                (∀ c, G c c) → IsDistribution D → 0 < α → 0 < β → β ≤ α → (K : ℝ) * α ≤ 1 → 
                (∀ i c, 0 < w i c) → (∀ i c, ρ i c ∈ Set.Icc (0 : ℝ) 1) → 
                ∑ ω : Fin C × Fin K, D ω.1 * mixProb α w ω.2 ω.1 * 
                  (S + (∑ c, D c * ρ (a c) c - ρ ω.2 ω.1) +
                    ∑ c, D c / (∑ c', if G c' c then D c' else 0) / β *
                      (Real.log (∑ i, w i c * Real.exp (β * 
                          (if i = ω.2 ∧ G ω.1 c then ρ i c / mixProb α w i ω.1 else 0)))
                        - Real.log (w (a c) c * Real.exp (β *
                          (if a c = ω.2 ∧ G ω.1 c then ρ (a c) c / mixProb α w (a c) ω.1 else 0)))))
                ≤ (S + ∑ c, D c / (∑ c', if G c' c then D c' else 0) / β *
                    (Real.log (∑ i, w i c) - Real.log (w (a c) c))) + (K * α + β / α) := by
              intro K C G D α β w ρ a S hG hD hα hβ hβα hKα hw hρ
              obtain ⟨hD0, hD1⟩ := hD
              have hne : ∀ c : Fin C, Nonempty (Fin K) := fun c => ⟨a c⟩
              have hW : ∀ c, 0 < ∑ i, w i c := fun c => by
                have := hne c
                exact Finset.sum_pos (fun i _ => hw i c) Finset.univ_nonempty
              obtain ⟨W, hWdef⟩ : ∃ W : Fin C → ℝ, ∀ c, W c = ∑ i, w i c := ⟨_, fun _ => rfl⟩
              simp only [← hWdef] at hW ⊢
              obtain ⟨u, hu⟩ : ∃ u : Fin K → Fin C → ℝ, ∀ i c, u i c = w i c / W c := ⟨_, fun _ _ => rfl⟩
              have hu0 : ∀ i c, 0 ≤ u i c := fun i c => by rw [hu]; exact div_nonneg (hw i c).le (hW c).le
              have hu1 : ∀ c, ∑ i, u i c = 1 := fun c => by
                simp only [hu]
                rw [← Finset.sum_div, ← hWdef, div_self (hW c).ne']
              obtain ⟨p, hp⟩ : ∃ p : Fin K → Fin C → ℝ, ∀ i c, p i c = mixProb α w i c :=
                ⟨_, fun _ _ => rfl⟩
              have hp' : ∀ i c, p i c = (1 - K * α) * u i c + α := fun i c => by
                rw [hp, mixProb, hu, hWdef]
              simp only [← hp]
              have hpα : ∀ i c, α ≤ p i c := fun i c => by
                rw [hp']
                have := mul_nonneg (sub_nonneg.mpr hKα) (hu0 i c)
                linarith
              have hp0 : ∀ i c, 0 < p i c := fun i c => hα.trans_le (hpα i c)
              have hp1 : ∀ c, ∑ i, p i c = 1 := fun c => by
                simp only [hp', Finset.sum_add_distrib, ← Finset.mul_sum, hu1]
                simp
              obtain ⟨f, hf⟩ : ∃ f : Fin C → ℝ, ∀ c, f c = ∑ c', if G c' c then D c' else 0 :=
                ⟨_, fun _ => rfl⟩
              simp only [← hf]
              have hDf : ∀ c, D c ≤ f c := fun c => by
                have := Finset.single_le_sum (f := fun c' => if G c' c then D c' else 0)
                  (s := Finset.univ) (fun c' _ => by split_ifs; exacts [hD0 _, le_rfl]) (Finset.mem_univ c)
                simpa [hG c, hf] using this
              obtain ⟨g, hg⟩ : ∃ g : Fin C → ℝ, ∀ c, g c = D c / f c := ⟨_, fun _ => rfl⟩
              have hg0 : ∀ c, 0 ≤ g c := fun c => by
                rw [hg]; exact div_nonneg (hD0 c) ((hD0 c).trans (hDf c))
              have hgf : ∀ c, g c * f c = D c := fun c => by
                rw [hg]
                rcases ((hD0 c).trans (hDf c)).eq_or_lt with h | h
                · rw [← h]; have := hDf c; have := hD0 c; simp; linarith
                · exact div_mul_cancel₀ _ h.ne'
              simp only [← hg]
              obtain ⟨X, hX⟩ : ∃ X : Fin C × Fin K → Fin K → Fin C → ℝ, ∀ ω i c, X ω i c =
                if i = ω.2 ∧ G ω.1 c then ρ i c / p i ω.1 else 0 := ⟨_, fun _ _ _ => rfl⟩
              simp only [← hX]
              have hX0 : ∀ ω i c, 0 ≤ X ω i c := fun ω i c => by
                rw [hX]; split_ifs
                · exact div_nonneg (hρ i c).1 (hp0 _ _).le
                · exact le_rfl
              have hXα : ∀ ω i c, β * X ω i c ≤ 1 := fun ω i c => by
                rw [hX]; split_ifs
                · rw [← mul_div_assoc, div_le_one (hp0 _ _)]
                  have h1 := hρ i c
                  have h2 := hpα i ω.1
                  nlinarith [h1.1, h1.2]
                · simp
              have hexp : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → Real.exp x ≤ 1 + x + x ^ 2 := by
                intro x h0 h1
                have := Real.abs_exp_sub_one_sub_id_le (x := x) (by rw [abs_of_nonneg h0]; exact h1)
                have := (abs_le.mp this).2
                linarith
              -- expectation
              obtain ⟨Q, hQ⟩ : ∃ Q : Fin C × Fin K → ℝ, ∀ ω, Q ω = D ω.1 * p ω.2 ω.1 := ⟨_, fun _ => rfl⟩
              simp only [← hQ]
              have hQ0 : ∀ ω, 0 ≤ Q ω := fun ω => by rw [hQ]; exact mul_nonneg (hD0 _) (hp0 _ _).le
              have hQ1 : ∑ ω, Q ω = 1 := by
                simp only [hQ, Fintype.sum_prod_type, ← Finset.mul_sum, hp1, mul_one, hD1]
              have hEX : ∀ i c, ∑ ω, Q ω * X ω i c = f c * ρ i c := fun i c => by
                simp only [hQ, hX, Fintype.sum_prod_type]
                rw [hf, Finset.sum_mul]
                refine Finset.sum_congr rfl (fun c' _ => ?_)
                rw [Finset.sum_eq_single i]
                · by_cases h : G c' c
                  · simp only [h, and_self, if_true]
                    have := (hp0 i c').ne'
                    field_simp
                  · simp [h]
                · intro j _ hj
                  simp [Ne.symm hj]
                · simp
              have hEX2 : ∀ i c, ∑ ω, Q ω * X ω i c ^ 2 ≤ f c / α := fun i c => by
                calc ∑ ω, Q ω * X ω i c ^ 2 ≤ ∑ ω, (Q ω * X ω i c) / α := by
                      refine Finset.sum_le_sum (fun ω _ => ?_)
                      have : X ω i c ≤ 1 / α := by
                        rw [hX]; split_ifs
                        · rw [div_le_div_iff₀ (hp0 _ _) hα]
                          have h1 := hρ i c
                          have h2 := hpα i ω.1
                          nlinarith [h1.1, h1.2]
                        · positivity
                      have h2 := mul_le_mul_of_nonneg_left this (mul_nonneg (hQ0 ω) (hX0 ω i c))
                      calc Q ω * X ω i c ^ 2 = Q ω * X ω i c * X ω i c := by ring
                        _ ≤ _ := h2
                        _ = _ := by ring
                  _ = f c * ρ i c / α := by rw [← Finset.sum_div, hEX]
                  _ ≤ _ := by
                      refine div_le_div_of_nonneg_right ?_ hα.le
                      exact mul_le_of_le_one_right ((hD0 c).trans (hDf c)) (hρ i c).2
              have hEρ : ∑ ω, Q ω * ρ ω.2 ω.1 = ∑ c, D c * ∑ j, p j c * ρ j c := by
                simp only [hQ, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]
              have hlog : ∀ ω c, Real.log (∑ i, w i c * Real.exp (β * X ω i c)) ≤
                  Real.log (W c) + ∑ i, u i c * (β * X ω i c + β ^ 2 * X ω i c ^ 2) := by
                intro ω c
                have := hne c
                have hpos : 0 < ∑ i, w i c * Real.exp (β * X ω i c) :=
                  Finset.sum_pos (fun i _ => mul_pos (hw i c) (Real.exp_pos _)) Finset.univ_nonempty
                have h1 : ∑ i, w i c * Real.exp (β * X ω i c) = 
                    W c * ∑ i, u i c * Real.exp (β * X ω i c) := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl (fun i _ => ?_)
                  rw [hu]; have := (hW c).ne'; field_simp
                rw [h1] at hpos ⊢
                have hpos2 : 0 < ∑ i, u i c * Real.exp (β * X ω i c) := 
                  (mul_pos_iff_of_pos_left (hW c)).mp hpos
                rw [Real.log_mul (hW c).ne' hpos2.ne']
                have h2 := Real.log_le_sub_one_of_pos hpos2
                have h3 : ∑ i, u i c * Real.exp (β * X ω i c) ≤ 
                    1 + ∑ i, u i c * (β * X ω i c + β ^ 2 * X ω i c ^ 2) := by
                  rw [← hu1 c, ← Finset.sum_add_distrib]
                  refine Finset.sum_le_sum (fun i _ => ?_)
                  have := mul_le_mul_of_nonneg_left (hexp _ (mul_nonneg hβ.le (hX0 ω i c)) (hXα ω i c)) 
                    (hu0 i c)
                  refine this.trans (le_of_eq (by ring))
                linarith
              have hlog2 : ∀ ω c, Real.log (w (a c) c * Real.exp (β * X ω (a c) c)) =
                  Real.log (w (a c) c) + β * X ω (a c) c := by
                intro ω c
                rw [Real.log_mul (hw _ _).ne' (Real.exp_pos _).ne', Real.log_exp]
              obtain ⟨L, hL⟩ : ∃ L : Fin C → ℝ, ∀ c, L c = Real.log (W c) - Real.log (w (a c) c) :=
                ⟨_, fun _ => rfl⟩
              -- pointwise bound
              have hpt : ∀ ω, S + (∑ c, D c * ρ (a c) c - ρ ω.2 ω.1) + ∑ c, g c / β * 
                    (Real.log (∑ i, w i c * Real.exp (β * X ω i c)) -
                      Real.log (w (a c) c * Real.exp (β * X ω (a c) c))) ≤
                  S + (∑ c, D c * ρ (a c) c - ρ ω.2 ω.1) + ∑ c, g c / β * 
                    (L c + ∑ i, u i c * (β * X ω i c + β ^ 2 * X ω i c ^ 2) - β * X ω (a c) c) := by
                intro ω
                refine add_le_add_right (Finset.sum_le_sum (fun c _ => ?_)) _
                refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (hg0 c) hβ.le)
                rw [hlog2, hL]
                have := hlog ω c
                linarith
              have hEc : ∀ c, ∑ ω, Q ω * (g c / β * 
                    (L c + ∑ i, u i c * (β * X ω i c + β ^ 2 * X ω i c ^ 2) - β * X ω (a c) c)) ≤
                  g c / β * L c + D c * (∑ i, u i c * ρ i c + β / α - ρ (a c) c) := by
                intro c
                have e1 : ∑ ω, Q ω * (g c / β * 
                    (L c + ∑ i, u i c * (β * X ω i c + β ^ 2 * X ω i c ^ 2) - β * X ω (a c) c)) =
                    g c / β * (L c + ∑ i, u i c * (β * (∑ ω, Q ω * X ω i c) + 
                      β ^ 2 * (∑ ω, Q ω * X ω i c ^ 2)) - β * ∑ ω, Q ω * X ω (a c) c) := by
                  have e2 : ∑ i, u i c * (β * (∑ ω, Q ω * X ω i c) + β ^ 2 * (∑ ω, Q ω * X ω i c ^ 2)) =
                      ∑ ω, Q ω * ∑ i, u i c * (β * X ω i c + β ^ 2 * X ω i c ^ 2) := by
                    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
                    rw [Finset.sum_comm]
                    refine Finset.sum_congr rfl (fun ω _ => Finset.sum_congr rfl (fun i _ => ?_))
                    ring
                  have e3 : L c = ∑ ω, Q ω * L c := by rw [← Finset.sum_mul, hQ1, one_mul]
                  rw [e2]
                  conv_rhs => rw [e3]
                  simp only [Finset.mul_sum _ _ β]
                  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
                  refine Finset.sum_congr rfl (fun ω _ => ?_)
                  ring
                rw [e1]
                simp only [hEX]
                have h4 : ∑ i, u i c * (β * (f c * ρ i c) + β ^ 2 * (∑ ω, Q ω * X ω i c ^ 2)) ≤
                    β * f c * (∑ i, u i c * ρ i c + β / α) := by
                  calc _ ≤ ∑ i, u i c * (β * (f c * ρ i c) + β ^ 2 * (f c / α)) := by
                        refine Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left ?_ (hu0 i c))
                        have := mul_le_mul_of_nonneg_left (hEX2 i c) (sq_nonneg β)
                        linarith
                    _ = β * f c * ∑ i, u i c * ρ i c + (∑ i, u i c) * (β ^ 2 * (f c / α)) := by
                        rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
                        refine Finset.sum_congr rfl (fun i _ => ?_)
                        ring
                    _ = _ := by rw [hu1]; ring
                calc _ ≤ g c / β * (L c + β * f c * (∑ i, u i c * ρ i c + β / α) 
                          - β * (f c * ρ (a c) c)) := by
                      refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (hg0 c) hβ.le)
                      linarith
                  _ = g c / β * L c + (g c * f c) * (∑ i, u i c * ρ i c + β / α - ρ (a c) c) := by
                      have := hβ.ne'
                      field_simp
                      ring
                  _ = _ := by rw [hgf]
              have hup : ∀ c, ∑ i, u i c * ρ i c - ∑ j, p j c * ρ j c ≤ K * α := by
                intro c
                rw [← Finset.sum_sub_distrib]
                calc _ ≤ ∑ i, K * α * u i c := by
                      refine Finset.sum_le_sum (fun i _ => ?_)
                      rw [hp']
                      have h1 := hρ i c
                      have h3 : 0 ≤ K * α * u i c := mul_nonneg (by positivity) (hu0 i c)
                      have : u i c * ρ i c - ((1 - K * α) * u i c + α) * ρ i c = 
                        K * α * u i c * ρ i c - α * ρ i c := by ring
                      rw [this]
                      have h4 := mul_le_mul_of_nonneg_left h1.2 h3
                      have h5 := mul_nonneg hα.le h1.1
                      linarith
                  _ = _ := by rw [← Finset.mul_sum, hu1, mul_one]
              calc _ ≤ ∑ ω, Q ω * (S + (∑ c, D c * ρ (a c) c - ρ ω.2 ω.1) + ∑ c, g c / β * 
                    (L c + ∑ i, u i c * (β * X ω i c + β ^ 2 * X ω i c ^ 2) - β * X ω (a c) c)) :=
                    Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hpt ω) (hQ0 ω))
                _ = S + ∑ c, D c * ρ (a c) c - ∑ ω, Q ω * ρ ω.2 ω.1 + ∑ c, ∑ ω, Q ω * (g c / β * 
                    (L c + ∑ i, u i c * (β * X ω i c + β ^ 2 * X ω i c ^ 2) - β * X ω (a c) c)) := by
                    rw [Finset.sum_comm]
                    have e3 : S + ∑ c, D c * ρ (a c) c = ∑ ω, Q ω * (S + ∑ c, D c * ρ (a c) c) := by
                      rw [← Finset.sum_mul, hQ1, one_mul]
                    rw [e3, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
                    refine Finset.sum_congr rfl (fun ω _ => ?_)
                    rw [← Finset.mul_sum]
                    ring
                _ ≤ S + ∑ c, D c * ρ (a c) c - ∑ c, D c * ∑ j, p j c * ρ j c + ∑ c, 
                    (g c / β * L c + D c * (∑ i, u i c * ρ i c + β / α - ρ (a c) c)) := by
                    rw [hEρ]
                    exact add_le_add_right (Finset.sum_le_sum (fun c _ => hEc c)) _
                _ = S + ∑ c, g c / β * L c + ∑ c, D c * 
                    (∑ i, u i c * ρ i c - ∑ j, p j c * ρ j c + β / α) := by
                    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
                    ring
                _ ≤ S + ∑ c, g c / β * L c + ∑ c, D c * (K * α + β / α) := by
                    refine add_le_add_right (Finset.sum_le_sum (fun c _ => ?_)) _
                    refine mul_le_mul_of_nonneg_left ?_ (hD0 c)
                    have := hup c
                    linarith
                _ = _ := by
                    rw [← Finset.sum_mul, hD1, one_mul]
                    simp only [hL]
            refine ⟨3, ?_⟩
            intro K C T _ G hG D hD hKT r hr
            obtain ⟨R, hR01, hRr⟩ : ∃ R : ℕ → Fin K → Fin C → ℝ,
                (∀ n i c, R n i c ∈ Set.Icc (0 : ℝ) 1) ∧ ∀ t : Fin T, R t = r t := by
              refine ⟨fun n => if h : n < T then r ⟨n, h⟩ else fun _ _ => 0, ?_, ?_⟩
              · intro n i c
                by_cases h : n < T
                · simpa [h] using hr ⟨n, h⟩ i c
                · simp [h]
              · intro t
                simp
            have hamax : ∀ c, ∃ i : Fin K, Finset.univ.sup' Finset.univ_nonempty
                (fun i => ∑ t, r t i c) = ∑ t, r t i c := fun c => by
              obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin K))
                (fun i => ∑ t, r t i c)
              exact ⟨i, hi⟩
            choose a ha using hamax
            obtain ⟨H, hH⟩ : ∃ H : (n : ℕ) → (Fin n → Fin C × Fin K) → Fin n → Obs K C,
                ∀ n τ s, H n τ s = ((τ s).1, (τ s).2, fun c' => if G (τ s).1 c' then R s (τ s).2 c' else 0) :=
              ⟨_, fun _ _ _ => rfl⟩
            have hwpos : ∀ n (h : Fin n → Obs K C) i c, 0 < exp3CLUWeights T G n h i c := by
              intro n
              induction n with
              | zero => intro h i c; simp [exp3CLUWeights]
              | succ n ih =>
                intro h i c
                simp only [exp3CLUWeights]
                split_ifs
                · exact mul_pos (ih _ _ _) (Real.exp_pos _)
                · exact ih _ _ _
            obtain ⟨wt, hwt⟩ : ∃ wt : (n : ℕ) → (Fin n → Fin C × Fin K) → Fin K → Fin C → ℝ,
                ∀ n τ, wt n τ = exp3CLUWeights T G n (H n τ) := ⟨_, fun _ _ => rfl⟩
            have hwt0 : ∀ n τ i c, 0 < wt n τ i c := fun n τ i c => by rw [hwt]; exact hwpos _ _ _ _
            obtain ⟨α, hα⟩ : ∃ α, α = exp3CLUAlpha K T := ⟨_, rfl⟩
            obtain ⟨β, hβ⟩ : ∃ β, β = exp3CLUBeta K T := ⟨_, rfl⟩
            have hwsucc : ∀ n τ ω i c, wt (n+1) (Fin.snoc (α := fun _ => Fin C × Fin K) τ ω) i c =
                wt n τ i c * Real.exp (β * 
                  (if i = ω.2 ∧ G ω.1 c then R n i c / mixProb α (wt n τ) i ω.1 else 0)) := by
              intro n τ ω i c
              have e1 : (fun s : Fin n => H (n+1) (Fin.snoc (α := fun _ => Fin C × Fin K) τ ω) s.castSucc)
                  = H n τ := by
                funext s
                rw [hH, hH, Fin.snoc_castSucc]
                rfl
              have e2 : H (n+1) (Fin.snoc (α := fun _ => Fin C × Fin K) τ ω) (Fin.last n) =
                  (ω.1, ω.2, fun c' => if G ω.1 c' then R n ω.2 c' else 0) := by
                rw [hH, Fin.snoc_last]
                rfl
              rw [hwt (n+1), hwt n, exp3CLUWeights]
              simp only [e1, e2, ← hα, ← hβ]
              by_cases h : i = ω.2 ∧ G ω.1 c
              · obtain ⟨h1, h2⟩ := h
                subst h1
                simp only [h2, and_self, if_true, mul_div_assoc]
              · simp only [if_neg h, mul_zero, Real.exp_zero, mul_one]
            obtain ⟨q, hq⟩ : ∃ q : (n : ℕ) → (Fin n → Fin C × Fin K) → Fin C × Fin K → ℝ,
                ∀ n τ ω, q n τ ω = D ω.1 * mixProb α (wt n τ) ω.2 ω.1 := ⟨_, fun _ _ _ => rfl⟩
            have hPP : ∀ τ, trajProb (fun _ : Fin K => G) D (exp3CLU T G) r τ =
                ∏ t : Fin T, q t (fun s => τ (Fin.castLE t.2.le s)) (τ t) := by
              intro τ
              unfold trajProb
              refine Finset.prod_congr rfl (fun t _ => ?_)
              have e1 : hist (fun _ : Fin K => G) r τ t = H t (fun s => τ (Fin.castLE t.2.le s)) := by
                funext s
                rw [hH]
                have := hRr (Fin.castLE t.2.le s)
                simp only [Fin.val_castLE] at this
                simp only [hist, this]
                rfl
              rw [hq, e1, exp3CLU, hwt, hα]
            obtain ⟨Red, hRed⟩ : ∃ Red : (n : ℕ) → (Fin n → Fin C × Fin K) → ℝ, ∀ n τ, Red n τ =
                ∑ s : Fin n, (∑ c, D c * R s (a c) c - R s (τ s).2 (τ s).1) := ⟨_, fun _ _ => rfl⟩
            have hRedS : ∀ n τ ω, Red (n+1) (Fin.snoc (α := fun _ => Fin C × Fin K) τ ω) =
                Red n τ + (∑ c, D c * R n (a c) c - R n ω.2 ω.1) := by
              intro n τ ω
              rw [hRed, hRed, Fin.sum_univ_castSucc]
              simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
            have hreg : (∑ τ : Fin T → Fin C × Fin K, 
                  ∏ t : Fin T, q t (fun s => τ (Fin.castLE t.2.le s)) (τ t)) = 1 →
                exAnteRegret (fun _ : Fin K => G) D (exp3CLU T G) r = 
                ∑ τ : Fin T → Fin C × Fin K, 
                  (∏ t : Fin T, q t (fun s => τ (Fin.castLE t.2.le s)) (τ t)) * Red T τ := by
              intro h1
              have e1 : ∀ τ, Red T τ = exAnteBenchmark D r - ∑ t, r t (τ t).2 (τ t).1 := by
                intro τ
                rw [hRed, Finset.sum_sub_distrib]
                simp only [hRr, exAnteBenchmark, ha, Finset.mul_sum]
                rw [Finset.sum_comm]
              simp only [e1, mul_sub, Finset.sum_sub_distrib]
              rw [← Finset.sum_mul, h1, one_mul]
              simp only [exAnteRegret, algReward, expect, hPP]
            rcases Nat.lt_or_ge 1 K with hK | hK
            · obtain ⟨hα0, hβ0, hA0, hβα, hKα, hLβ, hTb⟩ := num K T (by exact_mod_cast hK) hKT α β _ 
                (by rw [hα]; rfl) (by rw [hβ, hα]; rfl) rfl
              have hwS : ∀ n τ c, 0 < ∑ i, wt n τ i c := fun n τ c =>
                Finset.sum_pos (fun i _ => hwt0 n τ i c) Finset.univ_nonempty
              have hmix0 : ∀ n τ i c, 0 ≤ mixProb α (wt n τ) i c := fun n τ i c => by
                rw [mixProb]
                exact add_nonneg (mul_nonneg (sub_nonneg.mpr hKα)
                  (div_nonneg (hwt0 n τ i c).le (hwS n τ c).le)) hα0.le
              have hmix1 : ∀ n τ c, ∑ i, mixProb α (wt n τ) i c = 1 := fun n τ c => by
                simp only [mixProb, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
                rw [div_self (hwS n τ c).ne']
                simp
              obtain ⟨hP1, hE⟩ := key (Fin C × Fin K) q (fun n τ => Red n τ +
                  ∑ c, D c / (∑ c', if G c' c then D c' else 0) / β *
                    (Real.log (∑ i, wt n τ i c) - Real.log (wt n τ (a c) c))) (K * α + β / α)
                (fun n τ ω => by rw [hq]; exact mul_nonneg (hD.1 _) (hmix0 _ _ _ _))
                (fun n τ => by
                  simp only [hq, Fintype.sum_prod_type, ← Finset.mul_sum, hmix1, mul_one, hD.2])
                (fun n τ => by
                  simp only [hq, hRedS, hwsucc]
                  exact drift K C G D α β (wt n τ) (R n) a (Red n τ) hG hD hα0 hβ0 hβα hKα (hwt0 n τ)
                    (hR01 n)) T
              rw [hreg hP1]
              have hl1 := lem1 C G hG D hD.1
              have hDf : ∀ c, D c ≤ ∑ c', if G c' c then D c' else 0 := fun c => by
                have := Finset.single_le_sum (f := fun c' => if G c' c then D c' else 0)
                  (s := Finset.univ) (fun c' _ => by split_ifs; exacts [hD.1 _, le_rfl]) (Finset.mem_univ c)
                simpa [hG c] using this
              have hg0 : ∀ c, 0 ≤ D c / (∑ c', if G c' c then D c' else 0) := fun c =>
                div_nonneg (hD.1 c) ((hD.1 c).trans (hDf c))
              have hlam : (1 : ℝ) ≤ maxAcyclicNumber G := by
                refine le_trans ?_ hl1
                rw [← hD.2]
                refine Finset.sum_le_sum (fun c _ => ?_)
                have hf1 : (∑ c', if G c' c then D c' else 0) ≤ 1 := by
                  rw [← hD.2]
                  refine Finset.sum_le_sum (fun c' _ => ?_)
                  split_ifs
                  · exact le_rfl
                  · exact hD.1 c'
                rcases (hD.1 c).eq_or_lt with h | h
                · rw [← h]; simp
                · rw [le_div_iff₀ (h.trans_le (hDf c))]
                  exact mul_le_of_le_one_right h.le hf1
              have hP0 : ∀ τ : Fin T → Fin C × Fin K, 
                  0 ≤ ∏ t : Fin T, q t (fun s => τ (Fin.castLE t.2.le s)) (τ t) := fun τ =>
                Finset.prod_nonneg (fun t _ => by rw [hq]; exact mul_nonneg (hD.1 _) (hmix0 _ _ _ _))
              have hstep : ∑ τ : Fin T → Fin C × Fin K, 
                  (∏ t : Fin T, q t (fun s => τ (Fin.castLE t.2.le s)) (τ t)) * Red T τ ≤ 
                  ∑ τ : Fin T → Fin C × Fin K, 
                  (∏ t : Fin T, q t (fun s => τ (Fin.castLE t.2.le s)) (τ t)) * (Red T τ +
                  ∑ c, D c / (∑ c', if G c' c then D c' else 0) / β *
                    (Real.log (∑ i, wt T τ i c) - Real.log (wt T τ (a c) c))) := by
                refine Finset.sum_le_sum (fun τ _ => mul_le_mul_of_nonneg_left ?_ (hP0 τ))
                refine le_add_of_nonneg_right (Finset.sum_nonneg (fun c _ => ?_))
                refine mul_nonneg (div_nonneg (hg0 c) hβ0.le) (sub_nonneg.mpr ?_)
                exact Real.log_le_log (hwt0 _ _ _ _)
                  (Finset.single_le_sum (f := fun i => wt T τ i c) (fun i _ => (hwt0 T τ i c).le)
                    (Finset.mem_univ (a c)))
              have hΦ0 : Red 0 Fin.elim0 + ∑ c, D c / (∑ c', if G c' c then D c' else 0) / β *
                    (Real.log (∑ i, wt 0 Fin.elim0 i c) - Real.log (wt 0 Fin.elim0 (a c) c)) =
                  (∑ c, D c / (∑ c', if G c' c then D c' else 0)) * (Real.log K / β) := by
                rw [hRed, Finset.sum_mul]
                simp only [hwt, exp3CLUWeights]
                simp
                refine Finset.sum_congr rfl (fun c _ => ?_)
                ring
              have hfin := hstep.trans hE
              rw [hΦ0, hLβ, hTb] at hfin
              refine hfin.trans ?_
              generalize (K : ℝ) ^ (1 / 3 : ℝ) = x1 at *
              generalize (T : ℝ) ^ (2 / 3 : ℝ) = x2 at *
              generalize Real.log (K : ℝ) ^ (1 / 3 : ℝ) = x3 at *
              have h1 := mul_le_mul_of_nonneg_right hl1 hA0
              have h2 := mul_le_mul_of_nonneg_right hlam hA0
              have h3 : 3 * (maxAcyclicNumber G : ℝ) * x1 * x2 * x3 = 
                3 * ((maxAcyclicNumber G : ℝ) * (x1 * x2 * x3)) := by ring
              rw [h3]
              linarith
            · have hK1 : K = 1 := le_antisymm hK (Nat.pos_of_ne_zero (NeZero.ne K))
              subst hK1
              have hα0 : α = 0 := by
                rw [hα, exp3CLUAlpha]; simp
              have hmix : ∀ n τ i c, mixProb α (wt n τ) i c = 1 := fun n τ i c => by
                have e : i = 0 := Subsingleton.elim _ _
                subst e
                rw [mixProb, hα0]
                simp [(hwt0 n τ 0 c).ne']
              obtain ⟨hP1, hE⟩ := key (Fin C × Fin 1) q Red 0
                (fun n τ ω => by rw [hq, hmix]; simpa using hD.1 _)
                (fun n τ => by simp [hq, hmix, Fintype.sum_prod_type, hD.2])
                (fun n τ => by
                  simp only [hq, hRedS, hmix, mul_one, Fintype.sum_prod_type, mul_add, mul_sub,
                    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.univ_unique, 
                    Finset.sum_singleton, ← Finset.sum_mul, hD.2, one_mul]
                  have : ∀ c, a c = default := fun c => Subsingleton.elim _ _
                  simp [this]) T
              rw [hreg hP1]
              refine hE.trans ?_
              rw [hRed]
              simp
