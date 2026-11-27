-- Prove2me | solution 1 for BayesProphet.MultiSec.Supplement.matching_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:39:30.557181+00:00
-- url     : https://prove2.me/submissions/e7bab011-6999-41f2-bacb-e4b0d2429ce3

import Mathlib
import Definitions.Def_BayesProphet_MultiSec_Supplement_Matching

open BayesProphet
open BayesProphet.MultiSec
open BayesProphet.MultiSec.Supplement

theorem solution {d n : ℕ} (adj : Fin d → Fin n → Bool) (r : Fin d → Fin n → ℝ)
    (hr : ∀ i j, 0 ≤ r i j) (z₁ z₂ : Fin n → ℝ) (hz₁ : ∀ j, 0 ≤ z₁ j) (hz₂ : ∀ j, 0 ≤ z₂ j)
    (b : Fin d → ℝ) (hb : ∀ i, 0 ≤ b i) (x₁ : Fin d → Fin n → ℝ)
    (hx₁ : x₁ ∈ matchOpt adj r z₁ b) :
    ∃ x₂ ∈ matchOpt adj r z₂ b, ‖x₁ - x₂‖ ≤ ∑ j, |z₁ j - z₂ j| := by
      classical
      -- closedness / compactness
      have hclosed : ∀ z : Fin n → ℝ, IsClosed (matchFeas (d := d) z b) := by
        intro z
        have : matchFeas z b = (⋂ i, {x : Fin d → Fin n → ℝ | ∑ j, x i j ≤ b i}) ∩
            ((⋂ j, {x : Fin d → Fin n → ℝ | ∑ i, x i j ≤ z j}) ∩
              ⋂ i, ⋂ j, {x : Fin d → Fin n → ℝ | 0 ≤ x i j}) := by
          ext x; simp [matchFeas]
        rw [this]
        refine IsClosed.inter (isClosed_iInter fun i => isClosed_le (by fun_prop) (by fun_prop))
          (IsClosed.inter (isClosed_iInter fun j => isClosed_le (by fun_prop) (by fun_prop))
            (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_le (by fun_prop) (by fun_prop)))
      have hF2c : IsCompact (matchFeas (d := d) z₂ b) := by
        have hK : IsCompact (Set.pi Set.univ fun i : Fin d =>
            Set.pi Set.univ fun _ : Fin n => Set.Icc (0:ℝ) (b i)) :=
          isCompact_univ_pi fun i => isCompact_univ_pi fun _ => isCompact_Icc
        refine hK.of_isClosed_subset (hclosed z₂) ?_
        intro x hx
        simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
        intro i j
        refine ⟨hx.2.2 i j, le_trans ?_ (hx.1 i)⟩
        exact Finset.single_le_sum (fun j _ => hx.2.2 i j) (Finset.mem_univ j)
      have hfc : Continuous (fun x : Fin d → Fin n → ℝ => ∑ i, ∑ j, x i j * r i j * adjR adj i j) := by
        fun_prop
      have hO2closed : IsClosed (matchOpt adj r z₂ b) := by
        have : matchOpt adj r z₂ b = matchFeas z₂ b ∩ ⋂ x' ∈ matchFeas z₂ b,
            {x : Fin d → Fin n → ℝ | ∑ i, ∑ j, x' i j * r i j * adjR adj i j ≤
              ∑ i, ∑ j, x i j * r i j * adjR adj i j} := by
          ext x; simp [matchOpt]
        rw [this]
        exact (hclosed z₂).inter (isClosed_biInter fun x' _ => isClosed_le continuous_const hfc)
      have hO2c : IsCompact (matchOpt adj r z₂ b) := hF2c.of_isClosed_subset hO2closed (fun x hx => hx.1)
      have h0 : (0 : Fin d → Fin n → ℝ) ∈ matchFeas z₂ b := by
        refine ⟨fun i => by simpa using hb i, fun j => by simpa using hz₂ j, fun i j => by simp⟩
      obtain ⟨x0, hx0F, hx0max⟩ := hF2c.exists_isMaxOn ⟨0, h0⟩ hfc.continuousOn
      have hx0O : x0 ∈ matchOpt adj r z₂ b := ⟨hx0F, fun x' hx' => hx0max hx'⟩
      have hΦc : Continuous (fun x : Fin d → Fin n → ℝ => ∑ i, ∑ j, |x i j - x₁ i j|) := by fun_prop
      obtain ⟨x₂, hx₂O, hx₂min⟩ := hO2c.exists_isMinOn ⟨x0, hx0O⟩ hΦc.continuousOn
      refine ⟨x₂, hx₂O, ?_⟩

      obtain ⟨hx₁F, hx₁opt⟩ := hx₁
      obtain ⟨hx₂F, hx₂opt⟩ := hx₂O
      obtain ⟨D, hD⟩ : ∃ D : Fin d → Fin n → ℝ, ∀ i j, D i j = x₂ i j - x₁ i j := ⟨_, fun _ _ => rfl⟩
      obtain ⟨A, hA1, hA2, hA3, hA4⟩ : ∃ A : Fin d ⊕ Fin n → Fin d ⊕ Fin n → Prop,
          (∀ i j, A (.inl i) (.inr j) ↔ 0 < D i j) ∧ (∀ i j, A (.inr j) (.inl i) ↔ D i j < 0) ∧
          (∀ i i', ¬ A (.inl i) (.inl i')) ∧ (∀ j j', ¬ A (.inr j) (.inr j')) :=
        ⟨fun u v => Sum.elim (fun i => Sum.elim (fun _ => False) (fun j => 0 < D i j) v)
          (fun j => Sum.elim (fun i => D i j < 0) (fun _ => False) v) u, by simp⟩
      -- KEY: no feasible conformal perturbation
      have hsmall : ∀ (ι : Type) [Fintype ι] (α β : ι → ℝ), (∀ k, 0 ≤ β k) →
          (∀ k, α k ≤ 0 ∨ 0 < β k) → ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0), ∀ k, ε * α k ≤ β k := by
        intro ι _ α β hβ h
        rw [Filter.eventually_all]
        intro k
        rcases h k with h | h
        · filter_upwards [self_mem_nhdsWithin] with ε hε
          have : (0:ℝ) < ε := hε
          nlinarith [hβ k]
        · have ht : Filter.Tendsto (fun ε : ℝ => ε * α k) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
            have : Filter.Tendsto (fun ε : ℝ => ε * α k) (nhds 0) (nhds (0 * α k)) :=
              (continuous_id.mul continuous_const).tendsto 0
            rw [zero_mul] at this
            exact this.mono_left nhdsWithin_le_nhds
          exact (ht.eventually (gt_mem_nhds h)).mono (fun _ h => h.le)
      have KEY : ∀ P : Fin d → Fin n → ℝ, (∀ i j, 0 ≤ P i j * D i j) → (∀ i j, D i j = 0 → P i j = 0) →
          (∀ i, 0 < ∑ j, P i j → ∑ j, x₁ i j < b i) → (∀ i, ∑ j, P i j < 0 → ∑ j, x₂ i j < b i) →
          (∀ j, 0 < ∑ i, P i j → ∑ i, x₁ i j < z₁ j) → (∀ j, ∑ i, P i j < 0 → ∑ i, x₂ i j < z₂ j) →
          P = 0 := by
        intro P hPD hP0 hr1 hr2 hc1 hc2
        by_contra hPne
        have e1 := hsmall (Fin d × Fin n) (fun p => |P p.1 p.2|) (fun p => |D p.1 p.2|)
          (fun p => abs_nonneg _) (fun p => by
            by_cases h : D p.1 p.2 = 0
            · left; simp [hP0 _ _ h]
            · right; exact abs_pos.2 h)
        have e2 := hsmall (Fin d) (fun i => ∑ j, P i j) (fun i => b i - ∑ j, x₁ i j)
          (fun i => by linarith [hx₁F.1 i]) (fun i => by
            by_cases h : 0 < ∑ j, P i j
            · right; linarith [hr1 i h]
            · left; linarith)
        have e3 := hsmall (Fin d) (fun i => -∑ j, P i j) (fun i => b i - ∑ j, x₂ i j)
          (fun i => by linarith [hx₂F.1 i]) (fun i => by
            by_cases h : ∑ j, P i j < 0
            · right; linarith [hr2 i h]
            · left; linarith)
        have e4 := hsmall (Fin n) (fun j => ∑ i, P i j) (fun j => z₁ j - ∑ i, x₁ i j)
          (fun j => by linarith [hx₁F.2.1 j]) (fun j => by
            by_cases h : 0 < ∑ i, P i j
            · right; linarith [hc1 j h]
            · left; linarith)
        have e5 := hsmall (Fin n) (fun j => -∑ i, P i j) (fun j => z₂ j - ∑ i, x₂ i j)
          (fun j => by linarith [hx₂F.2.1 j]) (fun j => by
            by_cases h : ∑ i, P i j < 0
            · right; linarith [hc2 j h]
            · left; linarith)
        obtain ⟨ε, ⟨⟨⟨⟨he1, he2⟩, he3⟩, he4⟩, he5⟩, hεpos⟩ :=
          (((((e1.and e2).and e3).and e4).and e5).and self_mem_nhdsWithin).exists
        have hε : (0:ℝ) < ε := hεpos
        have hent : ∀ i j, 0 ≤ x₁ i j + ε * P i j ∧ 0 ≤ x₂ i j - ε * P i j ∧
            |x₂ i j - ε * P i j - x₁ i j| = |x₂ i j - x₁ i j| - ε * |P i j| := by
          intro i j
          have h1 := he1 (i, j)
          have h2 := hPD i j
          have hx1 := hx₁F.2.2 i j
          have hx2 := hx₂F.2.2 i j
          simp only at h1
          rcases lt_trichotomy (D i j) 0 with h | h | h
          · have hP : P i j ≤ 0 := by by_contra hc; push_neg at hc; nlinarith
            rw [abs_of_nonpos hP, abs_of_neg h] at h1
            rw [hD] at h h1
            rw [abs_of_nonpos hP, abs_of_neg h, abs_of_nonpos (by nlinarith)]
            refine ⟨by nlinarith, by nlinarith, by ring⟩
          · have hP := hP0 i j h
            rw [hD] at h
            rw [hP]; simp [hx1, hx2, h]
          · have hP : 0 ≤ P i j := by by_contra hc; push_neg at hc; nlinarith
            rw [abs_of_nonneg hP, abs_of_pos h] at h1
            rw [hD] at h h1
            rw [abs_of_nonneg hP, abs_of_pos h, abs_of_nonneg (by nlinarith)]
            refine ⟨by nlinarith, by nlinarith, by ring⟩
        have hy1 : (fun i j => x₁ i j + ε * P i j) ∈ matchFeas z₁ b := by
          refine ⟨fun i => ?_, fun j => ?_, fun i j => (hent i j).1⟩
          · have := he2 i
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]; linarith
          · have := he4 j
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]; linarith
        have hy2 : (fun i j => x₂ i j - ε * P i j) ∈ matchFeas z₂ b := by
          refine ⟨fun i => ?_, fun j => ?_, fun i j => (hent i j).2.1⟩
          · have := he3 i
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; linarith
          · have := he5 j
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; linarith
        have hf1 : ∑ i, ∑ j, (x₁ i j + ε * P i j) * r i j * adjR adj i j =
            ∑ i, ∑ j, x₁ i j * r i j * adjR adj i j + ε * ∑ i, ∑ j, P i j * r i j * adjR adj i j := by
          simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
        have hf2 : ∑ i, ∑ j, (x₂ i j - ε * P i j) * r i j * adjR adj i j =
            ∑ i, ∑ j, x₂ i j * r i j * adjR adj i j - ε * ∑ i, ∑ j, P i j * r i j * adjR adj i j := by
          simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
        have hopt1 := hx₁opt _ hy1
        rw [hf1] at hopt1
        have hfP : ε * ∑ i, ∑ j, P i j * r i j * adjR adj i j ≤ 0 := by linarith
        have hy2O : (fun i j => x₂ i j - ε * P i j) ∈ matchOpt adj r z₂ b := by
          refine ⟨hy2, fun x' hx' => ?_⟩
          have := hx₂opt x' hx'
          simp only
          rw [hf2]; linarith
        have hmin := hx₂min hy2O
        simp only [Set.mem_setOf_eq] at hmin
        have hΦ : ∑ i, ∑ j, |x₂ i j - ε * P i j - x₁ i j| =
            ∑ i, ∑ j, |x₂ i j - x₁ i j| - ε * ∑ i, ∑ j, |P i j| := by
          simp only [fun i j => (hent i j).2.2, Finset.mul_sum, ← Finset.sum_sub_distrib]
        have hpos : 0 < ∑ i, ∑ j, |P i j| := by
          obtain ⟨i, j, hij⟩ : ∃ i j, P i j ≠ 0 := by
            by_contra hc; push_neg at hc; exact hPne (funext fun i => funext fun j => hc i j)
          have h1 : |P i j| ≤ ∑ j, |P i j| :=
            Finset.single_le_sum (f := fun j => |P i j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
          have h2 : ∑ j, |P i j| ≤ ∑ i, ∑ j, |P i j| :=
            Finset.single_le_sum (f := fun i => ∑ j, |P i j|)
              (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
          have := abs_pos.2 hij
          linarith
        have : ε * ∑ i, ∑ j, |P i j| > 0 := mul_pos hε hpos
        linarith

      have ARC : ∀ u v, A u v → ∃ P : Fin d → Fin n → ℝ, (∀ i j, 0 ≤ P i j * D i j) ∧
          (∀ i j, D i j = 0 → P i j = 0) ∧ (∃ i j, 0 < P i j * D i j) ∧
          (∀ i, ∑ j, P i j = (if (Sum.inl i : Fin d ⊕ Fin n) = u then 1 else 0) -
            (if (Sum.inl i : Fin d ⊕ Fin n) = v then 1 else 0)) ∧
          (∀ j, ∑ i, P i j = (if (Sum.inr j : Fin d ⊕ Fin n) = v then 1 else 0) -
            (if (Sum.inr j : Fin d ⊕ Fin n) = u then 1 else 0)) := by
        intro u v huv
        rcases u with i | j <;> rcases v with i' | j'
        · exact absurd huv (hA3 i i')
        · have h := (hA1 i j').1 huv
          refine ⟨fun i₀ j₀ => if i₀ = i then (if j₀ = j' then 1 else 0) else 0, ?_, ?_,
            ⟨i, j', by simpa using h⟩, ?_, ?_⟩
          · intro i₀ j₀
            by_cases h1 : i₀ = i <;> by_cases h2 : j₀ = j' <;> simp [h1, h2, h.le]
          · intro i₀ j₀ h0
            by_cases h1 : i₀ = i <;> by_cases h2 : j₀ = j' <;> simp [h1, h2] <;> subst h1 h2 <;> linarith
          · intro i₀; by_cases h1 : i₀ = i <;> simp [h1]
          · intro j₀; by_cases h1 : j₀ = j' <;> simp [h1]
        · have h := (hA2 i' j).1 huv
          refine ⟨fun i₀ j₀ => if i₀ = i' then (if j₀ = j then -1 else 0) else 0, ?_, ?_,
            ⟨i', j, by simpa using h⟩, ?_, ?_⟩
          · intro i₀ j₀
            by_cases h1 : i₀ = i' <;> by_cases h2 : j₀ = j <;> simp [h1, h2, h.le]
          · intro i₀ j₀ h0
            by_cases h1 : i₀ = i' <;> by_cases h2 : j₀ = j <;> simp [h1, h2] <;> subst h1 h2 <;> linarith
          · intro i₀; by_cases h1 : i₀ = i' <;> simp [h1]
          · intro j₀; by_cases h1 : j₀ = j <;> simp [h1]
        · exact absurd huv (hA4 j j')
      have WALK : ∀ u v, Relation.TransGen A u v → ∃ P : Fin d → Fin n → ℝ, (∀ i j, 0 ≤ P i j * D i j) ∧
          (∀ i j, D i j = 0 → P i j = 0) ∧ (∃ i j, 0 < P i j * D i j) ∧
          (∀ i, ∑ j, P i j = (if (Sum.inl i : Fin d ⊕ Fin n) = u then 1 else 0) -
            (if (Sum.inl i : Fin d ⊕ Fin n) = v then 1 else 0)) ∧
          (∀ j, ∑ i, P i j = (if (Sum.inr j : Fin d ⊕ Fin n) = v then 1 else 0) -
            (if (Sum.inr j : Fin d ⊕ Fin n) = u then 1 else 0)) := by
        intro u v huv
        induction huv with
        | single h => exact ARC _ _ h
        | tail _ hbc ih =>
          obtain ⟨P, hP1, hP2, -, hP4, hP5⟩ := ih
          obtain ⟨E, hE1, hE2, ⟨i₀, j₀, hE3⟩, hE4, hE5⟩ := ARC _ _ hbc
          refine ⟨fun i j => P i j + E i j, fun i j => ?_, fun i j h => ?_, ⟨i₀, j₀, ?_⟩,
            fun i => ?_, fun j => ?_⟩
          · have := hP1 i j; have := hE1 i j; simp only [add_mul]; linarith
          · simp [hP2 i j h, hE2 i j h]
          · have := hP1 i₀ j₀; simp only [add_mul]; linarith
          · rw [Finset.sum_add_distrib, hP4, hE4]; ring
          · rw [Finset.sum_add_distrib, hP5, hE5]; ring
      have CYC : ∀ u, ¬ Relation.TransGen A u u := by
        intro u hu
        obtain ⟨P, hP1, hP2, ⟨i₀, j₀, hP3⟩, hP4, hP5⟩ := WALK u u hu
        have := KEY P hP1 hP2 (fun i h => by rw [hP4] at h; simp at h)
          (fun i h => by rw [hP4] at h; simp at h) (fun j h => by rw [hP5] at h; simp at h)
          (fun j h => by rw [hP5] at h; simp at h)
        rw [this] at hP3; simp at hP3
      have hrow : ∀ i, ∑ j, D i j = ∑ j, x₂ i j - ∑ j, x₁ i j := fun i => by
        simp only [hD, Finset.sum_sub_distrib]
      have hcol : ∀ j, ∑ i, D i j = ∑ i, x₂ i j - ∑ i, x₁ i j := fun j => by
        simp only [hD, Finset.sum_sub_distrib]
      have hiden : ∀ (p : Fin d → ℝ) (q : Fin n → ℝ), ∑ i, ∑ j, (p i - q j) * D i j =
          ∑ i, p i * ∑ j, D i j - ∑ j, q j * ∑ i, D i j := by
        intro p q
        simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
        congr 1
        exact Finset.sum_comm
      set Δ := ∑ j, |z₁ j - z₂ j| with hΔdef
      have hΔ : 0 ≤ Δ := Finset.sum_nonneg fun _ _ => abs_nonneg _
      have GEN : ∀ u v, A u v →
          Δ < ∑ i, ∑ j, ((if Relation.ReflTransGen A (.inl i) u then (1:ℝ) else 0) -
            (if Relation.ReflTransGen A (.inr j) u then (1:ℝ) else 0)) * D i j →
          ∑ i, ∑ j, ((if Relation.ReflTransGen A v (.inl i) then (1:ℝ) else 0) -
            (if Relation.ReflTransGen A v (.inr j) then (1:ℝ) else 0)) * D i j < -Δ → False := by
        intro u v huv hU hS
        rw [hiden] at hU hS
        obtain ⟨t, hvt, ht1, ht2⟩ : ∃ t, Relation.ReflTransGen A v t ∧
            (∀ i, t = .inl i → ∑ j, x₂ i j < b i) ∧ (∀ j, t = .inr j → ∑ i, x₁ i j < z₁ j) := by
          by_contra hno
          have hR : ∀ i, Relation.ReflTransGen A v (.inl i) → b i ≤ ∑ j, x₂ i j := fun i hi => by
            by_contra hlt; push_neg at hlt
            exact hno ⟨_, hi, fun i' h' => by simp at h'; subst h'; exact hlt, fun j h' => by simp at h'⟩
          have hC : ∀ j, Relation.ReflTransGen A v (.inr j) → z₁ j ≤ ∑ i, x₁ i j := fun j hj => by
            by_contra hlt; push_neg at hlt
            exact hno ⟨_, hj, fun i h' => by simp at h', fun j' h' => by simp at h'; subst h'; exact hlt⟩
          have h1 : 0 ≤ ∑ i, (if Relation.ReflTransGen A v (.inl i) then (1:ℝ) else 0) * ∑ j, D i j := by
            refine Finset.sum_nonneg fun i _ => ?_
            split_ifs with h
            · rw [hrow]; linarith [hR i h, hx₁F.1 i]
            · simp
          have h2 : ∑ j, (if Relation.ReflTransGen A v (.inr j) then (1:ℝ) else 0) * ∑ i, D i j ≤ Δ := by
            refine Finset.sum_le_sum fun j _ => ?_
            split_ifs with h
            · rw [hcol, one_mul, abs_sub_comm]; linarith [hC j h, hx₂F.2.1 j, le_abs_self (z₂ j - z₁ j)]
            · simp
          linarith
        obtain ⟨s, hsu, hs1, hs2⟩ : ∃ s, Relation.ReflTransGen A s u ∧
            (∀ i, s = .inl i → ∑ j, x₁ i j < b i) ∧ (∀ j, s = .inr j → ∑ i, x₂ i j < z₂ j) := by
          by_contra hno
          have hR : ∀ i, Relation.ReflTransGen A (.inl i) u → b i ≤ ∑ j, x₁ i j := fun i hi => by
            by_contra hlt; push_neg at hlt
            exact hno ⟨_, hi, fun i' h' => by simp at h'; subst h'; exact hlt, fun j h' => by simp at h'⟩
          have hC : ∀ j, Relation.ReflTransGen A (.inr j) u → z₂ j ≤ ∑ i, x₂ i j := fun j hj => by
            by_contra hlt; push_neg at hlt
            exact hno ⟨_, hj, fun i h' => by simp at h', fun j' h' => by simp at h'; subst h'; exact hlt⟩
          have h1 : ∑ i, (if Relation.ReflTransGen A (.inl i) u then (1:ℝ) else 0) * ∑ j, D i j ≤ 0 := by
            refine Finset.sum_nonpos fun i _ => ?_
            split_ifs with h
            · rw [hrow]; linarith [hR i h, hx₂F.1 i]
            · simp
          have h2 : -Δ ≤ ∑ j, (if Relation.ReflTransGen A (.inr j) u then (1:ℝ) else 0) * ∑ i, D i j := by
            rw [hΔdef, ← Finset.sum_neg_distrib]
            refine Finset.sum_le_sum fun j _ => ?_
            split_ifs with h
            · rw [hcol, one_mul]; linarith [hC j h, hx₁F.2.1 j, le_abs_self (z₁ j - z₂ j)]
            · simp
          linarith
        have hst : Relation.TransGen A s t :=
          Relation.TransGen.trans_right hsu (Relation.TransGen.head' huv hvt)
        obtain ⟨P, hP1, hP2, ⟨i₀, j₀, hP3⟩, hP4, hP5⟩ := WALK s t hst
        have := KEY P hP1 hP2
          (fun i h => by
            rw [hP4] at h
            by_cases hsi : (Sum.inl i : Fin d ⊕ Fin n) = s
            · exact hs1 i hsi.symm
            · rw [if_neg hsi] at h; split_ifs at h <;> linarith)
          (fun i h => by
            rw [hP4] at h
            by_cases hti : (Sum.inl i : Fin d ⊕ Fin n) = t
            · exact ht1 i hti.symm
            · rw [if_neg hti] at h; split_ifs at h <;> linarith)
          (fun j h => by
            rw [hP5] at h
            by_cases hti : (Sum.inr j : Fin d ⊕ Fin n) = t
            · exact ht2 j hti.symm
            · rw [if_neg hti] at h; split_ifs at h <;> linarith)
          (fun j h => by
            rw [hP5] at h
            by_cases hsi : (Sum.inr j : Fin d ⊕ Fin n) = s
            · exact hs2 j hsi.symm
            · rw [if_neg hsi] at h; split_ifs at h <;> linarith)
        rw [this] at hP3; simp at hP3
      have hSnonpos : ∀ v i j, ((if Relation.ReflTransGen A v (.inl i) then (1:ℝ) else 0) -
          (if Relation.ReflTransGen A v (.inr j) then (1:ℝ) else 0)) * D i j ≤ 0 := by
        intro v i j
        by_cases h1 : Relation.ReflTransGen A v (.inl i) <;>
          by_cases h2 : Relation.ReflTransGen A v (.inr j) <;> simp only [h1, h2, if_true, if_false]
        · simp
        · have : D i j ≤ 0 := by
            by_contra hc; push_neg at hc; exact h2 (h1.tail ((hA1 i j).2 hc))
          linarith
        · have : 0 ≤ D i j := by
            by_contra hc; push_neg at hc; exact h1 (h2.tail ((hA2 i j).2 hc))
          linarith
        · simp
      have hUnonneg : ∀ u i j, 0 ≤ ((if Relation.ReflTransGen A (.inl i) u then (1:ℝ) else 0) -
          (if Relation.ReflTransGen A (.inr j) u then (1:ℝ) else 0)) * D i j := by
        intro u i j
        by_cases h1 : Relation.ReflTransGen A (.inl i) u <;>
          by_cases h2 : Relation.ReflTransGen A (.inr j) u <;> simp only [h1, h2, if_true, if_false]
        · simp
        · have : 0 ≤ D i j := by
            by_contra hc; push_neg at hc; exact h2 (Relation.ReflTransGen.head ((hA2 i j).2 hc) h1)
          linarith
        · have : D i j ≤ 0 := by
            by_contra hc; push_neg at hc; exact h1 (Relation.ReflTransGen.head ((hA1 i j).2 hc) h2)
          linarith
        · simp
      have hsingle : ∀ g : Fin d → Fin n → ℝ, (∀ i j, 0 ≤ g i j) → ∀ a b', g a b' ≤ ∑ i, ∑ j, g i j := by
        intro g hg a b'
        have h1 : g a b' ≤ ∑ j, g a j :=
          Finset.single_le_sum (f := fun j => g a j) (fun _ _ => hg _ _) (Finset.mem_univ b')
        have h2 : ∑ j, g a j ≤ ∑ i, ∑ j, g i j :=
          Finset.single_le_sum (f := fun i => ∑ j, g i j)
            (fun _ _ => Finset.sum_nonneg fun _ _ => hg _ _) (Finset.mem_univ a)
        linarith
      have hsingle' : ∀ g : Fin d → Fin n → ℝ, (∀ i j, g i j ≤ 0) → ∀ a b', ∑ i, ∑ j, g i j ≤ g a b' := by
        intro g hg a b'
        have := hsingle (fun i j => -g i j) (fun i j => by linarith [hg i j]) a b'
        simp only [Finset.sum_neg_distrib] at this
        linarith
      have hmain : ∀ a b', |D a b'| ≤ Δ := by
        intro a b'
        by_contra hlt
        push_neg at hlt
        rcases lt_trichotomy (D a b') 0 with h | h | h
        · have huv := (hA2 a b').2 h
          have hnc : ¬ Relation.ReflTransGen A (.inl a) (.inr b') :=
            fun hc => CYC _ (Relation.TransGen.head' huv hc)
          refine GEN _ _ huv ?_ ?_
          · refine lt_of_lt_of_le hlt (le_trans (le_of_eq ?_) (hsingle _ (hUnonneg (.inr b')) a b'))
            simp [hnc, abs_of_neg h, Relation.ReflTransGen.refl]
          · refine lt_of_le_of_lt (hsingle' _ (hSnonpos (.inl a)) a b') ?_
            simp [hnc, Relation.ReflTransGen.refl]; rw [abs_of_neg h] at hlt; linarith
        · rw [h] at hlt; simp at hlt; linarith
        · have huv := (hA1 a b').2 h
          have hnc : ¬ Relation.ReflTransGen A (.inr b') (.inl a) :=
            fun hc => CYC _ (Relation.TransGen.head' huv hc)
          refine GEN _ _ huv ?_ ?_
          · refine lt_of_lt_of_le hlt (le_trans (le_of_eq ?_) (hsingle _ (hUnonneg (.inl a)) a b'))
            simp [hnc, abs_of_pos h, Relation.ReflTransGen.refl]
          · refine lt_of_le_of_lt (hsingle' _ (hSnonpos (.inr b')) a b') ?_
            simp [hnc, Relation.ReflTransGen.refl]; rw [abs_of_pos h] at hlt; linarith
      refine (pi_norm_le_iff_of_nonneg hΔ).2 fun i => (pi_norm_le_iff_of_nonneg hΔ).2 fun j => ?_
      rw [Pi.sub_apply, Pi.sub_apply, Real.norm_eq_abs, abs_sub_comm, ← hD]
      exact hmain i j
