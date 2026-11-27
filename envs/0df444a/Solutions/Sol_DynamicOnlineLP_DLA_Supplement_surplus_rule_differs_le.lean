-- Prove2me | solution 1 for DynamicOnlineLP.DLA.Supplement.surplus_rule_differs_le
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T05:52:30.516619+00:00
-- url     : https://prove2.me/submissions/0b6bc337-afc1-4ad4-a65a-9521cedc38a9

import Mathlib
import Definitions.Def_DynamicOnlineLP_DLA_Supplement_SimplexPackingLP
import Definitions.Def_DynamicOnlineLP_DLA_Supplement_SurplusRule
import Definitions.Def_DynamicOnlineLP_DLA_Supplement_GeneralPosition

open DynamicOnlineLP.DLA.Supplement

open Classical in
/-- Lemma 8 (Agrawal–Wang–Ye 2014, p. 886), on any finite set `S` of arrivals: under general
position, for every optimal primal solution `x*` and every optimal dual resource price `p*` of
the simplex packing LP, and for every way of breaking ties, the vectors `x*_t` and `x_t(p*)`
differ at no more than `m` arrivals. -/
theorem solution {ι : Type} {m k : ℕ} (S : Finset ι) (f : ι → Fin k → ℝ)
    (g : ι → Fin m → Fin k → ℝ) (d : Fin m → ℝ) (x : ι → Fin k → ℝ) (p : Fin m → ℝ)
    (c : ι → Option (Fin k))
    (hGP : BlockGeneralPositionOn S f g)
    (hx : IsBlockPrimalOptimal S f g d x)
    (hp : IsBlockOptimalPrice S f g d p)
    (hc : ∀ t ∈ S, IsSurplusChoice (f t) (g t) p (c t)) :
    (S.filter (fun t => x t ≠ choiceVec (c t))).card ≤ m := by
      classical
      obtain ⟨⟨hxG, hxS⟩, hxopt⟩ := hx
      obtain ⟨y, ⟨hp0, hyS⟩, hyopt⟩ := hp
      set v := blockPrimalObj S f x with hv
      -- linearity helper
      have hlin : ∀ (B : Type) [Fintype B] (w : B → ℝ) (X : B → ι → Fin k → ℝ) (h : ι → Fin k → ℝ),
          ∑ t ∈ S, ∑ j, h t j * (∑ a, w a * X a t j) = ∑ a, w a * ∑ t ∈ S, ∑ j, h t j * X a t j := by
        intro B _ w X h
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm (s := (Finset.univ : Finset B)) (t := S)]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        refine Finset.sum_congr rfl fun a _ => ?_
        ring
      let Gi : Fin m → (ι → Fin k → ℝ) → ℝ := fun i z => ∑ t ∈ S, ∑ j, g t i j * z t j
      have hfub : ∀ (pp : Fin m → ℝ) (z : ι → Fin k → ℝ),
          ∑ i, pp i * Gi i z = ∑ t ∈ S, ∑ j, (∑ i, pp i * g t i j) * z t j := by
        intro pp z
        simp only [Gi, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      have hsplit : ∀ (pp : Fin m → ℝ) (z : ι → Fin k → ℝ),
          blockPrimalObj S f z = ∑ t ∈ S, ∑ j, surplus (f t) (g t) pp j * z t j + ∑ i, pp i * Gi i z := by
        intro pp z
        rw [hfub, ← Finset.sum_add_distrib]
        simp only [blockPrimalObj]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [surplus]; ring
      have hscore : ∀ (pp : Fin m → ℝ) (t : ι) (u : Option (Fin k)),
          ∑ j, surplus (f t) (g t) pp j * choiceVec u j = score (f t) (g t) pp u := by
        intro pp t u
        rcases u with _ | r
        · simp [choiceVec, score]
        · rw [Finset.sum_eq_single r]
          · simp [choiceVec, score]
          · intro b _ hb; simp [choiceVec, Ne.symm hb]
          · intro h; exact absurd (Finset.mem_univ r) h
      -- Step 1: strong duality
      have hSD : blockDualObj S d p y ≤ v := by
        apply le_of_forall_pos_lt_add
        intro ε hε
        let A := Option ((↥S) → Option (Fin k))
        let X : A → ι → Fin k → ℝ := fun a =>
          a.elim x (fun σ t j => if h : t ∈ S then choiceVec (σ ⟨t, h⟩) j else 0)
        let F : A → Option (Fin m) → ℝ := fun a o =>
          o.elim (blockPrimalObj S f (X a) - v - ε) (fun i => d i - Gi i (X a))
        have hXs : ∀ a, ∀ t ∈ S, (∀ j, 0 ≤ X a t j) ∧ ∑ j, X a t j ≤ 1 := by
          intro a t ht
          rcases a with _ | σ
          · exact hxS t ht
          · simp only [X, Option.elim, dif_pos ht]
            refine ⟨fun j => by unfold choiceVec; split_ifs <;> norm_num, ?_⟩
            rcases σ ⟨t, ht⟩ with _ | r <;> simp [choiceVec]
        let L : (A → ℝ) →ₗ[ℝ] (Option (Fin m) → ℝ) :=
          { toFun := fun w => ∑ a, w a • F a
            map_add' := by intro w1 w2; simp [add_smul, Finset.sum_add_distrib]
            map_smul' := by intro r w; simp [Finset.smul_sum, smul_smul] }
        have hLapp : ∀ w o, L w o = ∑ a, w a * F a o := by
          intro w o; simp [L, Finset.sum_apply]
        let K : Set (Option (Fin m) → ℝ) := L '' stdSimplex ℝ A
        have hKc : IsCompact K := (isCompact_stdSimplex ℝ A).image L.continuous_of_finiteDimensional
        have hKv : Convex ℝ K := (convex_stdSimplex ℝ A).linear_image L
        have hdisj : Disjoint K (ProperCone.positive ℝ (Option (Fin m) → ℝ) : Set _) := by
          rw [Set.disjoint_left]
          rintro _ ⟨w, hw, rfl⟩ hpos
          rw [SetLike.mem_coe, ProperCone.mem_positive] at hpos
          obtain ⟨hw0, hw1⟩ := hw
          let xw : ι → Fin k → ℝ := fun t j => ∑ a, w a * X a t j
          have hfeas : IsBlockFeasible S g d xw := by
            refine ⟨fun i => ?_, fun t ht => ⟨fun j => ?_, ?_⟩⟩
            · have h1 := hpos (some i)
              rw [Pi.zero_apply, hLapp] at h1
              simp only [F, Option.elim] at h1
              have h2 : ∑ a, w a * (d i - Gi i (X a)) = d i - ∑ a, w a * Gi i (X a) := by
                simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
              have h3 := hlin A w X (fun t j => g t i j)
              simp only [Gi] at h2 h1
              show ∑ t ∈ S, ∑ j, g t i j * (∑ a, w a * X a t j) ≤ d i
              linarith
            · exact Finset.sum_nonneg fun a _ => mul_nonneg (hw0 a) ((hXs a t ht).1 j)
            · show ∑ j, ∑ a, w a * X a t j ≤ 1
              rw [Finset.sum_comm]
              calc ∑ a, ∑ j, w a * X a t j = ∑ a, w a * ∑ j, X a t j := by
                    simp [Finset.mul_sum]
                _ ≤ ∑ a, w a * 1 := Finset.sum_le_sum fun a _ =>
                    mul_le_mul_of_nonneg_left (hXs a t ht).2 (hw0 a)
                _ = 1 := by simp [hw1]
          have h1 := hxopt xw hfeas
          have h2 := hpos none
          rw [Pi.zero_apply, hLapp] at h2
          simp only [F, Option.elim] at h2
          have h3 : ∑ a, w a * (blockPrimalObj S f (X a) - v - ε)
              = blockPrimalObj S f xw - v - ε := by
            have := hlin A w X f
            simp only [blockPrimalObj, xw]
            rw [this]
            simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
          linarith
        obtain ⟨ℓ, hℓC, hℓK⟩ := ProperCone.hyperplane_separation _ hKv hKc hdisj
        have hrep : ∀ z, ℓ z = ∑ o, z o * ℓ (Pi.single o 1) := by
          intro z
          conv_lhs => rw [← Finset.univ_sum_single z]
          rw [map_sum]
          refine Finset.sum_congr rfl fun o _ => ?_
          rw [← smul_eq_mul, ← ℓ.map_smul]
          congr 1
          ext o'
          simp [Pi.single_apply]
        set q : Option (Fin m) → ℝ := fun o => ℓ (Pi.single o 1) with hq
        have hq0 : ∀ o, 0 ≤ q o := by
          intro o
          apply hℓC
          rw [ProperCone.mem_positive]
          exact Pi.single_nonneg.2 zero_le_one
        have hFK : ∀ a, F a ∈ K := by
          intro a
          refine ⟨Pi.single a 1, single_mem_stdSimplex ℝ a, ?_⟩
          ext o
          rw [hLapp, Finset.sum_eq_single a]
          · simp
          · intro b _ hb; simp [Pi.single_apply, hb]
          · intro h; exact absurd (Finset.mem_univ a) h
        have hneg : ∀ a, q none * (blockPrimalObj S f (X a) - v - ε)
            + ∑ i, q (some i) * (d i - Gi i (X a)) < 0 := by
          intro a
          have := hℓK _ (hFK a)
          rw [hrep, Fintype.sum_option] at this
          simp only [F, Option.elim] at this
          have e : ∀ i, (d i - Gi i (X a)) * q (some i) = q (some i) * (d i - Gi i (X a)) :=
            fun i => mul_comm _ _
          simp only [hq] at e ⊢
          rw [Finset.sum_congr rfl fun i _ => e i] at this
          linarith
        have hlam : 0 < q none := by
          rcases (hq0 none).lt_or_eq with h | h
          · exact h
          · exfalso
            have h1 := hneg none
            rw [← h, zero_mul, zero_add] at h1
            have h2 : 0 ≤ ∑ i, q (some i) * (d i - Gi i (X none)) :=
              Finset.sum_nonneg fun i _ => mul_nonneg (hq0 _)
                (by simp only [Gi, X, Option.elim]; linarith [hxG i])
            linarith
        set lam := q none with hlamdef
        let p' : Fin m → ℝ := fun i => q (some i) / lam
        have hbr : ∀ t : ι, ∃ u : Option (Fin k),
            ∀ w, score (f t) (g t) p' w ≤ score (f t) (g t) p' u := by
          intro t
          obtain ⟨u, -, hu⟩ := Finset.exists_max_image Finset.univ (score (f t) (g t) p')
            Finset.univ_nonempty
          exact ⟨u, fun w => hu w (Finset.mem_univ _)⟩
        choose σ hσ using hbr
        let y' : ι → ℝ := fun t => score (f t) (g t) p' (σ t)
        have hfeas' : IsBlockDualFeasible S f g p' y' := by
          refine ⟨fun i => div_nonneg (hq0 _) hlam.le, fun t _ => ⟨?_, fun j => ?_⟩⟩
          · exact hσ t none
          · have h1 : score (f t) (g t) p' (some j) ≤ y' t := hσ t (some j)
            have h2 : score (f t) (g t) p' (some j) = f t j - ∑ i, p' i * g t i j := rfl
            show f t j ≤ ∑ i, p' i * g t i j + y' t
            linarith
        have hD := hyopt p' y' hfeas'
        let a0 : A := some (fun t => σ t.1)
        have hn := hneg a0
        have hid : blockPrimalObj S f (X a0) - ∑ i, p' i * Gi i (X a0) = ∑ t ∈ S, y' t := by
          rw [hsplit p', add_sub_cancel_right]
          refine Finset.sum_congr rfl fun t ht => ?_
          have : ∀ j, X a0 t j = choiceVec (σ t) j := by
            intro j; simp [X, a0, Option.elim, dif_pos ht]
          simp only [this]
          exact hscore p' t (σ t)
        have hq' : ∀ i, q (some i) = lam * p' i := fun i => by
          simp only [p']; field_simp
        simp only [hq'] at hn
        have hn2 : lam * ((blockPrimalObj S f (X a0) - v - ε)
            + ∑ i, p' i * (d i - Gi i (X a0))) < 0 := by
          rw [mul_add, Finset.mul_sum]; simpa [mul_assoc] using hn
        have hn3 : (blockPrimalObj S f (X a0) - v - ε) + ∑ i, p' i * (d i - Gi i (X a0)) < 0 := by
          by_contra h; push Not at h; have := mul_nonneg hlam.le h; linarith
        have hn4 : ∑ i, p' i * (d i - Gi i (X a0)) = ∑ i, d i * p' i - ∑ i, p' i * Gi i (X a0) := by
          rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun i _ => ?_; ring
        simp only [blockDualObj] at hD ⊢
        linarith
      -- Step 2: complementary slackness
      have hCS : ∀ t ∈ S, y t ≤ ∑ j, surplus (f t) (g t) p j * x t j := by
        have hP := hsplit p x
        have hpd : ∑ i, p i * Gi i x ≤ ∑ i, d i * p i := Finset.sum_le_sum fun i _ => by
          rw [mul_comm (d i)]; exact mul_le_mul_of_nonneg_left (hxG i) (hp0 i)
        have hle : ∀ t ∈ S, ∑ j, surplus (f t) (g t) p j * x t j ≤ y t := by
          intro t ht
          obtain ⟨hy0, hyf⟩ := hyS t ht
          obtain ⟨hx0, hx1⟩ := hxS t ht
          calc ∑ j, surplus (f t) (g t) p j * x t j ≤ ∑ j, y t * x t j :=
                Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right
                  (by simp only [surplus]; linarith [hyf j]) (hx0 j)
            _ = y t * ∑ j, x t j := by rw [Finset.mul_sum]
            _ ≤ y t * 1 := mul_le_mul_of_nonneg_left hx1 hy0
            _ = y t := mul_one _
        intro t ht
        by_contra hlt
        push Not at hlt
        have := Finset.sum_lt_sum hle ⟨t, ht, hlt⟩
        simp only [blockDualObj] at hSD
        rw [← hv] at hP
        linarith
      -- Step 3: untied arrivals follow the rule
      have hsub : S.filter (fun t => x t ≠ choiceVec (c t)) ⊆
          S.filter (fun t => IsTied (f t) (g t) p) := by
        intro t
        simp only [Finset.mem_filter]
        rintro ⟨ht, hne⟩
        refine ⟨ht, ?_⟩
        by_contra hT
        apply hne
        obtain ⟨hy0, hyf⟩ := hyS t ht
        obtain ⟨hx0, hx1⟩ := hxS t ht
        have hcs := hCS t ht
        have hc' := hc t ht
        have hyf' : ∀ j, surplus (f t) (g t) p j ≤ y t := fun j => by
          simp only [surplus]; linarith [hyf j]
        funext j
        rcases hct : c t with _ | r
        · rw [hct] at hc'
          simp only [IsSurplusChoice] at hc'
          have hng : ∀ j, surplus (f t) (g t) p j < 0 := by
            intro j
            rcases (hc' j).lt_or_eq with h | h
            · exact h
            · exfalso; apply hT
              refine ⟨none, some j, by simp, by simp [score, h], fun w => ?_⟩
              rcases w with _ | w
              · exact le_refl _
              · simpa [score] using hc' w
          have hnp : ∀ j ∈ (Finset.univ : Finset (Fin k)), surplus (f t) (g t) p j * x t j ≤ 0 :=
            fun j _ => mul_nonpos_of_nonpos_of_nonneg (hng j).le (hx0 j)
          have hs0 : ∑ j, surplus (f t) (g t) p j * x t j = 0 :=
            le_antisymm (Finset.sum_nonpos hnp) (by linarith)
          have := (Finset.sum_eq_zero_iff_of_nonpos hnp).1 hs0 j (Finset.mem_univ _)
          rcases mul_eq_zero.1 this with h | h
          · exact absurd h (hng j).ne
          · simp [choiceVec, h]
        · rw [hct] at hc'
          simp only [IsSurplusChoice] at hc'
          obtain ⟨hr0, hrmax⟩ := hc'
          set s := surplus (f t) (g t) p with hs
          have hlt : ∀ j, j ≠ r → s j < s r := by
            intro j hj
            rcases (hrmax j).lt_or_eq with h | h
            · exact h
            · exfalso; apply hT
              refine ⟨some r, some j, by simpa using Ne.symm hj, by simp only [score]; exact h.symm, fun w => ?_⟩
              rcases w with _ | w
              · simpa [score] using hr0.le
              · simpa [score] using hrmax w
          have hyr := hyf' r
          have hT0 : 0 ≤ ∑ j, (s r - s j) * x t j :=
            Finset.sum_nonneg fun j _ => mul_nonneg (by linarith [hrmax j]) (hx0 j)
          have hdec : ∑ j, s j * x t j = s r * ∑ j, x t j - ∑ j, (s r - s j) * x t j := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun j _ => ?_; ring
          have h1 : 0 ≤ s r * (1 - ∑ j, x t j) := mul_nonneg hr0.le (by linarith)
          have hTz : ∑ j, (s r - s j) * x t j = 0 := by nlinarith
          have hsum1 : ∑ j, x t j = 1 := by
            have h2 : s r * (1 - ∑ j, x t j) = 0 := by nlinarith
            rcases mul_eq_zero.1 h2 with h | h
            · exact absurd h hr0.ne'
            · linarith
          have hz : ∀ j, j ≠ r → x t j = 0 := by
            intro j hj
            have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
              mul_nonneg (by linarith [hrmax j]) (hx0 j))).1 hTz j (Finset.mem_univ _)
            rcases mul_eq_zero.1 this with h | h
            · linarith [hlt j hj]
            · exact h
          by_cases hj : j = r
          · subst hj
            rw [Finset.sum_eq_single j (fun b _ hb => hz b hb) (by simp)] at hsum1
            simp [choiceVec, hsum1]
          · rw [hz j hj]
            simp [choiceVec, Ne.symm hj]
      exact (Finset.card_le_card hsub).trans (hGP p)
