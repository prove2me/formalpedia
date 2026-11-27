-- Prove2me | solution 1 for BayesProphet.MultiSec.Supplement.lp_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:39:18.648652+00:00
-- url     : https://prove2.me/submissions/e1698e5e-355a-42df-88ab-79808f153dc7

import Mathlib
import Definitions.Def_BayesProphet_MultiSec_Supplement_Packing

open BayesProphet
open BayesProphet.MultiSec
open BayesProphet.MultiSec.Supplement

theorem solution {d n : ℕ} (A : Fin d → Fin n → ℕ) (μ : Seminorm ℝ (Fin n → ℝ))
    (hμ : ∀ y, μ y = 0 → y = 0) :
    ∃ κ : ℝ, IsLPLipschitzConst A μ κ := by
      classical
      -- linear map recording all the constraint rows and coordinates
      let L : (Fin n → ℝ) →ₗ[ℝ] ((Fin d ⊕ Fin n) → ℝ) :=
        { toFun := fun u k => Sum.elim (fun i => ∑ j, (A i j : ℝ) * u j) (fun j => u j) k
          map_add' := by
            intro u v
            funext k
            rcases k with i | j
            · simp [mul_add, Finset.sum_add_distrib]
            · simp
          map_smul' := by
            intro c u
            funext k
            rcases k with i | j
            · simp only [Sum.elim_inl, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
              exact Finset.sum_congr rfl fun j _ => by ring
            · simp }
      have hLl : ∀ u i, L u (Sum.inl i) = ∑ j, (A i j : ℝ) * u j := fun u i => rfl
      have hLr : ∀ u j, L u (Sum.inr j) = u j := fun u j => rfl
      -- representatives of sign patterns
      have hg : ∃ g : ((Fin d ⊕ Fin n) → SignType) → (Fin n → ℝ),
          ∀ z k, SignType.sign (L (g (fun k => SignType.sign (L z k))) k) = SignType.sign (L z k) := by
        refine ⟨fun σ => if h : ∃ u, ∀ k, SignType.sign (L u k) = σ k then h.choose else 0, ?_⟩
        intro z k
        have h : ∃ u, ∀ k, SignType.sign (L u k) = (fun k => SignType.sign (L z k)) k :=
          ⟨z, fun _ => rfl⟩
        simp only
        rw [dif_pos h]
        exact h.choose_spec k
      obtain ⟨g, hg⟩ := hg
      -- conformal decomposition
      have decomp : ∀ (m : ℕ) (z : Fin n → ℝ),
          (Finset.univ.filter (fun k => L z k ≠ 0)).card = m →
          ∃ l : ((Fin d ⊕ Fin n) → SignType) → ℝ, (∀ σ, 0 ≤ l σ) ∧ z = ∑ σ, l σ • g σ ∧
            ∀ σ k, (0 ≤ l σ * L (g σ) k ∧ l σ * L (g σ) k ≤ L z k) ∨
              (L z k ≤ l σ * L (g σ) k ∧ l σ * L (g σ) k ≤ 0) := by
        intro m
        induction m using Nat.strong_induction_on with
        | _ m ih =>
          intro z hm
          by_cases hz : (Finset.univ.filter (fun k => L z k ≠ 0)).Nonempty
          · obtain ⟨σ0, hσ0⟩ : ∃ σ0, σ0 = fun k => SignType.sign (L z k) := ⟨_, rfl⟩
            have hs := hg z
            rw [← hσ0] at hs
            have hpos : ∀ k, L z k ≠ 0 → 0 < L z k / L (g σ0) k := by
              intro k hk
              have := hs k
              rcases lt_or_gt_of_ne hk with h | h
              · rw [sign_neg h, sign_eq_neg_one_iff] at this
                exact div_pos_of_neg_of_neg h this
              · rw [sign_pos h, sign_eq_one_iff] at this
                exact div_pos h this
            obtain ⟨k0, hk0, hmin⟩ := Finset.exists_min_image _ (fun k => L z k / L (g σ0) k) hz
            obtain ⟨t, ht⟩ : ∃ t, t = L z k0 / L (g σ0) k0 := ⟨_, rfl⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk0 hmin
            rw [← ht] at hmin
            have htpos : 0 < t := ht ▸ hpos k0 hk0
            -- t * L g between 0 and L z
            have hbt : ∀ k, (0 ≤ t * L (g σ0) k ∧ t * L (g σ0) k ≤ L z k) ∨
                (L z k ≤ t * L (g σ0) k ∧ t * L (g σ0) k ≤ 0) := by
              intro k
              have hsk := hs k
              rcases lt_trichotomy (L z k) 0 with h | h | h
              · right
                rw [sign_neg h, sign_eq_neg_one_iff] at hsk
                have h1 := hmin k h.ne
                rw [le_div_iff_of_neg hsk] at h1
                exact ⟨h1, by nlinarith⟩
              · left
                rw [h, sign_zero, sign_eq_zero_iff] at hsk
                rw [hsk, h]; simp
              · left
                rw [sign_pos h, sign_eq_one_iff] at hsk
                have h1 := hmin k h.ne'
                rw [le_div_iff₀ hsk] at h1
                exact ⟨by positivity, h1⟩
            have hL' : ∀ k, L (z - t • g σ0) k = L z k - t * L (g σ0) k := by
              intro k; simp
            have hk0' : L (z - t • g σ0) k0 = 0 := by
              rw [hL', ht]
              have : L (g σ0) k0 ≠ 0 := by
                intro h0
                have := hs k0
                rw [h0, sign_zero] at this
                exact hk0 (sign_eq_zero_iff.1 this.symm)
              rw [div_mul_cancel₀ _ this, sub_self]
            have hlt : (Finset.univ.filter (fun k => L (z - t • g σ0) k ≠ 0)).card < m := by
              rw [← hm]
              apply Finset.card_lt_card
              refine ⟨?_, ?_⟩
              · intro k hk
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
                intro h0
                apply hk
                rw [hL']
                rcases hbt k with h | h <;> linarith [h.1, h.2]
              · intro hsub
                have := hsub (by simpa using hk0 : k0 ∈ Finset.univ.filter (fun k => L z k ≠ 0))
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
                exact this hk0'
            obtain ⟨l, hl0, hlz, hlb⟩ := ih _ hlt (z - t • g σ0) rfl
            refine ⟨fun σ => l σ + if σ = σ0 then t else 0, ?_, ?_, ?_⟩
            · intro σ
              have := hl0 σ
              dsimp only
              split_ifs <;> linarith
            · have : ∑ σ, (l σ + if σ = σ0 then t else 0) • g σ = (∑ σ, l σ • g σ) + t • g σ0 := by
                simp [add_smul, Finset.sum_add_distrib, ite_smul]
              rw [this, ← hlz]; simp
            · intro σ k
              have h1 := hlb σ k
              have h2 := hbt k
              rw [hL'] at h1
              dsimp only
              by_cases hσ : σ = σ0
              · subst hσ
                simp only [if_true]
                rw [add_mul]
                rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
                · left; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
                · right; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
                · left; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
                · right; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
              · simp only [hσ, if_false, add_zero]
                rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
                · left; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
                · right; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
                · left; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
                · right; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
          · have hz0 : ∀ k, L z k = 0 := by
              intro k
              by_contra h
              exact hz ⟨k, by simpa using h⟩
            refine ⟨fun _ => 0, fun _ => le_rfl, ?_, ?_⟩
            · funext j
              have := hz0 (Sum.inr j)
              rw [hLr] at this
              simp [this]
            · intro σ k
              left
              simp [hz0 k]
      -- comparison of the sup norm with μ
      have hnorm : ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Fin n → ℝ, ‖v‖ ≤ C * μ v := by
        have hcont : Continuous (fun v => μ v) := by
          have := (Seminorm.convexOn μ).continuousOn isOpen_univ
          exact continuousOn_univ.1 this
        by_cases hne : (Metric.sphere (0 : Fin n → ℝ) 1).Nonempty
        · obtain ⟨v0, hv0, hmin⟩ := (isCompact_sphere (0 : Fin n → ℝ) 1).exists_isMinOn hne
            hcont.continuousOn
          have hv0n : ‖v0‖ = 1 := by simpa using hv0
          have hpos : 0 < μ v0 := by
            rcases (apply_nonneg μ v0).lt_or_eq with h | h
            · exact h
            · have := hμ v0 h.symm
              rw [this] at hv0n
              simp at hv0n
          refine ⟨(μ v0)⁻¹, by positivity, fun v => ?_⟩
          by_cases hv : v = 0
          · simp [hv]
          · have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
            have hmem : (‖v‖⁻¹ • v) ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
              simp [norm_smul, hvn.ne']
            have h1 : μ v0 ≤ μ (‖v‖⁻¹ • v) := hmin hmem
            rw [map_smul_eq_mul, norm_inv, norm_norm] at h1
            rw [inv_mul_eq_div, le_div_iff₀ hvn] at h1
            rw [inv_mul_eq_div, le_div_iff₀ hpos]
            linarith
        · refine ⟨0, le_rfl, fun v => ?_⟩
          by_cases hv : v = 0
          · simp [hv]
          · exfalso
            have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
            exact hne ⟨‖v‖⁻¹ • v, by simp [norm_smul, hvn.ne']⟩
      obtain ⟨C, hC0, hC⟩ := hnorm
      obtain ⟨c, hc⟩ : ∃ c : ((Fin d ⊕ Fin n) → SignType) → ℝ, c = fun σ => ∑ j, |g σ j|⁻¹ := ⟨_, rfl⟩
      have hc0 : ∀ σ, 0 ≤ c σ := by
        intro σ; rw [hc]; exact Finset.sum_nonneg fun j _ => by positivity
      refine ⟨(∑ σ, c σ * ‖g σ‖) * C, ?_⟩
      intro b r y y₂ hy hy₂ x hx
      obtain ⟨hxf, hxo⟩ := hx
      -- nonempty
      have hb : ∀ i, 0 ≤ b i := fun i =>
        (Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (hxf.2 j).1).trans (hxf.1 i)
      have hcl : IsClosed (packFeas A b y₂) := by
        have : packFeas A b y₂ = (⋂ i, {x | ∑ j, (A i j : ℝ) * x j ≤ b i}) ∩
            ((⋂ j, {x | 0 ≤ x j}) ∩ (⋂ j, {x | x j ≤ y₂ j})) := by
          ext u
          simp only [packFeas, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, forall_and]
        rw [this]
        refine (isClosed_iInter fun i => isClosed_le (by fun_prop) (by fun_prop)).inter
          ((isClosed_iInter fun j => isClosed_le (by fun_prop) (by fun_prop)).inter
          (isClosed_iInter fun j => isClosed_le (by fun_prop) (by fun_prop)))
      have hcomp : IsCompact (packFeas A b y₂) :=
        (isCompact_Icc (a := (0 : Fin n → ℝ)) (b := y₂)).of_isClosed_subset hcl
          fun u hu => ⟨fun j => (hu.2 j).1, fun j => (hu.2 j).2⟩
      have hne : (packFeas A b y₂).Nonempty := ⟨0, by
        refine ⟨fun i => by simpa using hb i, fun j => ⟨le_rfl, hy₂ j⟩⟩⟩
      obtain ⟨w, hw, hwmax⟩ := hcomp.exists_isMaxOn hne
        (f := fun u => ∑ j, r j * u j) (by fun_prop)
      have hwo : w ∈ packOpt A r b y₂ := ⟨hw, fun u hu => hwmax hu⟩
      have hoeq : packOpt A r b y₂ = packFeas A b y₂ ∩ {u | ∑ j, r j * w j ≤ ∑ j, r j * u j} := by
        ext u
        constructor
        · intro hu
          exact ⟨hu.1, hu.2 w hw⟩
        · intro hu
          exact ⟨hu.1, fun v hv => (hwo.2 v hv).trans hu.2⟩
      have hocomp : IsCompact (packOpt A r b y₂) := by
        rw [hoeq]
        exact hcomp.inter_right (isClosed_le (by fun_prop) (by fun_prop))
      obtain ⟨x₂, hx₂, hmin⟩ := hocomp.exists_isMinOn ⟨w, hwo⟩
        (f := fun u => ∑ j, |u j - x j|) (by fun_prop)
      have hmin' : ∀ u ∈ packOpt A r b y₂, ∑ j, |x₂ j - x j| ≤ ∑ j, |u j - x j| := fun u hu => hmin hu
      refine ⟨x₂, hx₂, ?_⟩
      obtain ⟨δ, hδ⟩ : ∃ δ, δ = ‖y - y₂‖ := ⟨_, rfl⟩
      have hδ0 : 0 ≤ δ := hδ ▸ norm_nonneg _
      have hδj : ∀ j, |y j - y₂ j| ≤ δ := by
        intro j
        rw [hδ]
        exact norm_le_pi_norm (y - y₂) j
      obtain ⟨l, hl0, hlz, hlb⟩ := decomp _ (x₂ - x) rfl
      have hLz : ∀ k, L (x₂ - x) k = L x₂ k - L x k := by intro k; simp
      have hstep : ∀ σ, l σ * ‖g σ‖ ≤ c σ * ‖g σ‖ * δ := by
        intro σ
        suffices hj : g σ = 0 ∨ ∃ j, g σ j ≠ 0 ∧ l σ * |g σ j| ≤ δ by
          rcases hj with h | ⟨j, hj, hle⟩
          · simp [h]
          · have hjp : 0 < |g σ j| := abs_pos.2 hj
            have h1 : |g σ j|⁻¹ ≤ c σ := by
              rw [hc]
              exact Finset.single_le_sum (f := fun j => |g σ j|⁻¹) (fun j _ => by positivity)
                (Finset.mem_univ j)
            have h2 : l σ ≤ |g σ j|⁻¹ * δ := by
              rw [inv_mul_eq_div, le_div_iff₀ hjp]; exact hle
            have h3 : l σ ≤ c σ * δ := h2.trans (mul_le_mul_of_nonneg_right h1 hδ0)
            calc l σ * ‖g σ‖ ≤ (c σ * δ) * ‖g σ‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
              _ = _ := by ring
        by_contra hcon
        push Not at hcon
        obtain ⟨hgne, hbig⟩ := hcon
        obtain ⟨j0, hj0⟩ : ∃ j, g σ j ≠ 0 := by
          by_contra h
          push Not at h
          exact hgne (funext h)
        have hlpos : 0 < l σ := by
          rcases (hl0 σ).lt_or_eq with h | h
          · exact h
          · have := hbig j0 hj0
            rw [← h] at this
            linarith
        -- conformality for coordinates and rows, for all small ε
        have hcoord : ∀ j, (0 ≤ l σ * g σ j ∧ l σ * g σ j ≤ x₂ j - x j) ∨
            (x₂ j - x j ≤ l σ * g σ j ∧ l σ * g σ j ≤ 0) := by
          intro j
          have := hlb σ (Sum.inr j)
          rw [hLz] at this
          simpa only [hLr] using this
        have hcoord' : ∀ ε, 0 ≤ ε → ε ≤ l σ → ∀ j, (0 ≤ ε * g σ j ∧ ε * g σ j ≤ x₂ j - x j) ∨
            (x₂ j - x j ≤ ε * g σ j ∧ ε * g σ j ≤ 0) := by
          intro ε h0 h1 j
          rcases hcoord j with h | h
          · left
            have hgp : 0 ≤ g σ j := nonneg_of_mul_nonneg_right h.1 hlpos
            exact ⟨mul_nonneg h0 hgp, (mul_le_mul_of_nonneg_right h1 hgp).trans h.2⟩
          · right
            have hgp : g σ j ≤ 0 := by
              by_contra hh
              push Not at hh
              have := mul_pos hlpos hh
              linarith [h.2]
            exact ⟨h.1.trans (mul_le_mul_of_nonpos_right h1 hgp),
              mul_nonpos_of_nonneg_of_nonpos h0 hgp⟩
        have hrow : ∀ ε, 0 ≤ ε → ε ≤ l σ → ∀ i,
            (L x (Sum.inl i) + ε * L (g σ) (Sum.inl i) ≤ b i ∧
              L x₂ (Sum.inl i) - ε * L (g σ) (Sum.inl i) ≤ b i) := by
          intro ε h0 h1 i
          have hb1 : L x (Sum.inl i) ≤ b i := hxf.1 i
          have hb2 : L x₂ (Sum.inl i) ≤ b i := hx₂.1.1 i
          have h := hlb σ (Sum.inl i)
          rw [hLz] at h
          rcases h with h | h
          · have hgp : 0 ≤ L (g σ) (Sum.inl i) := nonneg_of_mul_nonneg_right h.1 hlpos
            have h2 := mul_le_mul_of_nonneg_right h1 hgp
            have h3 := mul_nonneg h0 hgp
            constructor <;> linarith [h.1, h.2]
          · have hgp : L (g σ) (Sum.inl i) ≤ 0 := by
              by_contra hh
              push Not at hh
              have := mul_pos hlpos hh
              linarith [h.2]
            have h2 := mul_le_mul_of_nonpos_right h1 hgp
            have h3 := mul_nonpos_of_nonneg_of_nonpos h0 hgp
            constructor <;> linarith [h.1, h.2]
        -- pick small ε
        have hsmall : ∀ a p q : ℝ, (a < p ∨ (a ≤ p ∧ q ≤ 0)) →
            ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), a + ε * q ≤ p := by
          intro a p q h
          rcases h with h | ⟨h, hq⟩
          · have ht : Filter.Tendsto (fun ε : ℝ => a + ε * q) (nhdsWithin 0 (Set.Ioi 0)) (nhds a) := by
              have : Continuous (fun ε : ℝ => a + ε * q) := by fun_prop
              have h2 := this.tendsto 0
              simp only [zero_mul, add_zero] at h2
              exact h2.mono_left nhdsWithin_le_nhds
            exact (ht.eventually (gt_mem_nhds h)).mono fun ε hε => hε.le
          · filter_upwards [self_mem_nhdsWithin] with ε hε
            have : ε * q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hε) hq
            linarith
        have hεpos : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ε := self_mem_nhdsWithin
        have hεl : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε ≤ l σ := by
          have := hsmall 0 (l σ) 1 (Or.inl hlpos)
          simpa using this
        rcases lt_or_ge 0 (∑ j, r j * g σ j) with hr | hr
        · have hy1 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ j, x j + ε * g σ j ≤ y j := by
            rw [Filter.eventually_all]
            intro j
            apply hsmall
            rcases le_or_gt (g σ j) 0 with h | h
            · exact Or.inr ⟨(hxf.2 j).2, h⟩
            · left
              rcases (hxf.2 j).2.lt_or_eq with h1 | h1
              · exact h1
              · exfalso
                have h2 := hbig j h.ne'
                rw [abs_of_pos h] at h2
                have h3 := (hx₂.1.2 j).2
                have h4 := hδj j
                have h5 := neg_abs_le (y j - y₂ j)
                have h6 := mul_pos hlpos h
                rcases hcoord j with h7 | h7 <;> linarith [h7.1, h7.2]
          obtain ⟨ε, h0, h1, h2⟩ := (hεpos.and (hεl.and hy1)).exists
          have hfeas : x + ε • g σ ∈ packFeas A b y := by
            refine ⟨fun i => ?_, fun j => ⟨?_, ?_⟩⟩
            · have := (hrow ε h0.le h1 i).1
              rw [← hLl]
              simpa using this
            · have h3 := (hxf.2 j).1
              have h4 := (hx₂.1.2 j).1
              simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              rcases hcoord' ε h0.le h1 j with h5 | h5 <;> linarith [h5.1, h5.2]
            · simpa using h2 j
          have h3 := hxo _ hfeas
          have h4 : ∑ j, r j * (x + ε • g σ) j = ∑ j, r j * x j + ε * ∑ j, r j * g σ j := by
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun j _ => ?_
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            ring
          have := mul_pos h0 hr
          linarith
        · have hy1 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ j, x₂ j + ε * (-g σ j) ≤ y₂ j := by
            rw [Filter.eventually_all]
            intro j
            apply hsmall
            rcases le_or_gt 0 (g σ j) with h | h
            · exact Or.inr ⟨(hx₂.1.2 j).2, by linarith⟩
            · left
              rcases (hx₂.1.2 j).2.lt_or_eq with h1 | h1
              · exact h1
              · exfalso
                have h2 := hbig j h.ne
                rw [abs_of_neg h] at h2
                have h3 := (hxf.2 j).2
                have h4 := hδj j
                have h5 := le_abs_self (y j - y₂ j)
                have h6 := mul_neg_of_pos_of_neg hlpos h
                rcases hcoord j with h7 | h7 <;> linarith [h7.1, h7.2]
          obtain ⟨ε, h0, h1, h2⟩ := (hεpos.and (hεl.and hy1)).exists
          have hfeas : x₂ - ε • g σ ∈ packFeas A b y₂ := by
            refine ⟨fun i => ?_, fun j => ⟨?_, ?_⟩⟩
            · have := (hrow ε h0.le h1 i).2
              rw [← hLl]
              simpa using this
            · have h3 := (hxf.2 j).1
              have h4 := (hx₂.1.2 j).1
              simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
              rcases hcoord' ε h0.le h1 j with h5 | h5 <;> linarith [h5.1, h5.2]
            · have := h2 j
              simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
              linarith
          have h4 : ∑ j, r j * (x₂ - ε • g σ) j = ∑ j, r j * x₂ j - ε * ∑ j, r j * g σ j := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun j _ => ?_
            simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
            ring
          have hopt : x₂ - ε • g σ ∈ packOpt A r b y₂ := by
            refine ⟨hfeas, fun u hu => ?_⟩
            have h5 := hx₂.2 u hu
            have h6 := mul_nonpos_of_nonneg_of_nonpos h0.le hr
            linarith
          have h5 := hmin' _ hopt
          have h6 : ∑ j, |(x₂ - ε • g σ) j - x j| < ∑ j, |x₂ j - x j| := by
            have hterm : ∀ j, |(x₂ - ε • g σ) j - x j| = |x₂ j - x j| - ε * |g σ j| := by
              intro j
              simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
              have he : ε * |g σ j| = |ε * g σ j| := by rw [abs_mul, abs_of_pos h0]
              rw [he]
              rcases hcoord' ε h0.le h1 j with h7 | h7
              · rw [abs_of_nonneg h7.1, abs_of_nonneg (h7.1.trans h7.2),
                  abs_of_nonneg (by linarith [h7.1, h7.2])]
                ring
              · rw [abs_of_nonpos h7.2, abs_of_nonpos (h7.1.trans h7.2),
                  abs_of_nonpos (by linarith [h7.1, h7.2])]
                ring
            apply Finset.sum_lt_sum
            · intro j _
              rw [hterm]
              have : 0 ≤ ε * |g σ j| := by positivity
              linarith
            · refine ⟨j0, Finset.mem_univ _, ?_⟩
              rw [hterm]
              have : 0 < ε * |g σ j0| := mul_pos h0 (abs_pos.2 hj0)
              linarith
          linarith
      calc ‖x - x₂‖ = ‖x₂ - x‖ := norm_sub_rev _ _
        _ = ‖∑ σ, l σ • g σ‖ := by rw [← hlz]
        _ ≤ ∑ σ, ‖l σ • g σ‖ := norm_sum_le _ _
        _ = ∑ σ, l σ * ‖g σ‖ := by
            refine Finset.sum_congr rfl fun σ _ => ?_
            rw [norm_smul, Real.norm_of_nonneg (hl0 σ)]
        _ ≤ ∑ σ, c σ * ‖g σ‖ * δ := Finset.sum_le_sum fun σ _ => hstep σ
        _ = (∑ σ, c σ * ‖g σ‖) * δ := by rw [Finset.sum_mul]
        _ ≤ (∑ σ, c σ * ‖g σ‖) * (C * μ (y - y₂)) := by
            refine mul_le_mul_of_nonneg_left (hδ ▸ hC _) ?_
            exact Finset.sum_nonneg fun σ _ => mul_nonneg (hc0 σ) (norm_nonneg _)
        _ = _ := by ring
