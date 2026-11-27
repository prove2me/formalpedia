-- Prove2me | solution 1 for ChenWhitt93.Reflection.Supplement.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:20:06.406675+00:00
-- url     : https://prove2.me/submissions/015d4b4a-6878-4e26-9dd9-821fbb885a87

import Mathlib
import Definitions.Def_ChenWhitt93_Reflection_Supplement_FixedUpDown

open ChenWhitt93
open ChenWhitt93.Reflection
open ChenWhitt93.Reflection.Supplement

open MeasureTheory Filter Topology Matrix
open ChenWhitt93.JumpDiffusion

/-- Lemma 5.1 (p. 356), in the pathwise (Skorohod-represented) form of its proof: under the
deterministic versions of the assumptions of Section 5 — Section 3's model for every network,
(4.6), (4.7), (5.2), (5.10), `P` substochastic with `Pᵏ → 0`, (4.1)–(4.4) and (5.1) holding
uniformly on compacts with continuous limits — every queue-length / busy-time solution
`(Zⁿ, Bⁿ)` satisfies `n⁻¹ Bⁿ(nt) → νt` uniformly on compact subsets of `[0, ∞)`, jointly in
`ℝᴶ`. -/
theorem solution {J : ℕ} (χ : Fin J → Fin J → ℕ → Bool) (net : ℕ → NetworkData J)
    (lamn mun nun : ℕ → Fin J → ℝ) (lam mu nu clam cmu cnu : Fin J → ℝ)
    (P : Matrix (Fin J) (Fin J) ℝ) (L : LimitData5 J)
    (Z : ℕ → ℝ → Fin J → ℤ) (B : ℕ → ℝ → Fin J → ℝ)
    (hH : PathwiseHyp5 χ net lamn mun nun lam mu nu clam cmu cnu P L)
    (hsol : ∀ n, IsQueueSolution χ (net n) (Z n) (B n)) :
    UocTendsto (fun (n : ℕ) (t : ℝ) (j : Fin J) => B n (n * t) j / n)
      (fun t j => nu j * t) := by
        obtain ⟨hvalid, hpar, hconv, hreg⟩ := hH
        obtain ⟨hlam, hlam0, hmu, hmu0, hnu, hnu01, hbal, hP⟩ := hpar
        obtain ⟨hZ0c, hAc, hSc, hRc, hDc⟩ := hconv
        obtain ⟨hAreg, hSreg, hRreg, hDreg⟩ := hreg
        obtain ⟨hPnn, hProw, hPpow⟩ := hP
        have hnn : ∀ n j k, 0 ≤ (net n).up j k ∧ 0 ≤ (net n).down j k := fun n => (hvalid n).1.1
        have hTmono : ∀ n j a b, a ≤ b → (net n).cycleStart j a ≤ (net n).cycleStart j b := by
          intro n j a b hab
          unfold Interruptions.cycleStart
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
          intro i _ _
          linarith [(hnn n j i).1, (hnn n j i).2]
        have hTsucc : ∀ n j l, (net n).cycleStart j (l+1)
            = (net n).cycleStart j l + ((net n).up j l + (net n).down j l) := by
          intro n j l; unfold Interruptions.cycleStart; rw [Finset.sum_range_succ]
        have hdisj : ∀ n j s, (net n).IsUp j s → ¬ (net n).IsDown j s := by
          rintro n j s ⟨l, h1, h2⟩ ⟨l', h3, h4⟩
          rcases lt_trichotomy l l' with h | h | h
          · have := hTmono n j (l+1) l' h
            have := hTsucc n j l
            linarith [(hnn n j l').1, (hnn n j l).2]
          · subst h; linarith
          · have := hTmono n j (l'+1) l h
            linarith
        have hcover : ∀ n j s, 0 ≤ s → (net n).IsUp j s ∨ (net n).IsDown j s := by
          intro n j s hs
          have hex : ∃ l, s < (net n).cycleStart j l :=
            (((hvalid n).1.2 j).eventually_gt_atTop s).exists
          classical
          obtain ⟨l, hl, hmin⟩ : ∃ l, s < (net n).cycleStart j l ∧ ∀ m < l, ¬ s < (net n).cycleStart j m :=
            ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
          have hl0 : l ≠ 0 := by
            intro h0
            have : (net n).cycleStart j 0 = 0 := by simp [Interruptions.cycleStart]
            rw [h0, this] at hl; linarith
          obtain ⟨l', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl0
          have hle : (net n).cycleStart j l' ≤ s := not_lt.mp (hmin l' (Nat.lt_succ_self l'))
          rw [hTsucc] at hl
          by_cases hu : s < (net n).cycleStart j l' + (net n).up j l'
          · exact Or.inl ⟨l', hle, hu⟩
          · right; refine ⟨l', not_lt.mp hu, ?_⟩; rw [hTsucc]; linarith
        have hDmeas : ∀ n j, MeasurableSet {s | (net n).IsDown j s} := by
          intro n j
          have : {s | (net n).IsDown j s} = ⋃ l, Set.Ico ((net n).cycleStart j l + (net n).up j l)
              ((net n).cycleStart j (l+1)) := by
            ext s; simp [Interruptions.IsDown]
          rw [this]; exact MeasurableSet.iUnion fun l => measurableSet_Ico
        obtain ⟨Y, hYdef⟩ : ∃ Y : ℕ → Fin J → ℝ → ℝ, ∀ n j s,
            Y n j s = s - (net n).downTime j s - B n s j :=
          ⟨fun n j s => s - (net n).downTime j s - B n s j, fun _ _ _ => rfl⟩
        have hBle : ∀ n j s, 0 ≤ s → 0 ≤ B n s j ∧ B n s j ≤ s := by
          intro n j s hs
          rw [(hsol n s hs j).2.2]
          refine ⟨measureReal_nonneg, ?_⟩
          calc volume.real {x | x ∈ Set.Icc 0 s ∧ 0 < Z n x j ∧ (net n).IsUp j x}
              ≤ volume.real (Set.Icc (0:ℝ) s) :=
                measureReal_mono (fun x hx => hx.1) measure_Icc_lt_top.ne
            _ = s := by rw [Real.volume_real_Icc]; simp [hs]
        have hDle : ∀ n j s, 0 ≤ s → 0 ≤ (net n).downTime j s ∧ (net n).downTime j s ≤ s := by
          intro n j s hs
          unfold Interruptions.downTime
          refine ⟨measureReal_nonneg, ?_⟩
          calc volume.real (Set.Icc 0 s ∩ {x | (net n).IsDown j x})
              ≤ volume.real (Set.Icc (0:ℝ) s) :=
                measureReal_mono Set.inter_subset_left measure_Icc_lt_top.ne
            _ = s := by rw [Real.volume_real_Icc]; simp [hs]
        have hY0 : ∀ n j, Y n j 0 = 0 := by
          intro n j
          have h1 := hBle n j 0 le_rfl
          have h2 := hDle n j 0 le_rfl
          rw [hYdef]; linarith
        have hYinc : ∀ n j a b, 0 ≤ a → a ≤ b →
            (0 ≤ Y n j b - Y n j a ∧ Y n j b - Y n j a ≤ b - a) ∧
            ((∀ s ∈ Set.Ioc a b, 0 < Z n s j) → Y n j b = Y n j a) := by
          intro n j a b ha hab
          have hb : 0 ≤ b := ha.trans hab
          set Dn := {x | (net n).IsDown j x} with hDn
          have hBinc : B n b j - B n a j = volume.real
              ({x | x ∈ Set.Icc 0 b ∧ 0 < Z n x j ∧ (net n).IsUp j x} ∩ Set.Ioc a b) := by
            rw [(hsol n b hb j).2.2, (hsol n a ha j).2.2]
            have hfin : volume {x | x ∈ Set.Icc 0 b ∧ 0 < Z n x j ∧ (net n).IsUp j x} ≠ ⊤ :=
              ((measure_mono (fun x hx => hx.1)).trans_lt (measure_Icc_lt_top (a := (0:ℝ)) (b := b))).ne
            have := measureReal_inter_add_sdiff (μ := volume) (s := {x | x ∈ Set.Icc 0 b ∧ 0 < Z n x j ∧ (net n).IsUp j x}) (t := Set.Ioc a b) measurableSet_Ioc hfin
            have hset : {x | x ∈ Set.Icc 0 b ∧ 0 < Z n x j ∧ (net n).IsUp j x} \ Set.Ioc a b
                = {x | x ∈ Set.Icc 0 a ∧ 0 < Z n x j ∧ (net n).IsUp j x} := by
              ext s; simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_Icc, Set.mem_Ioc]
              constructor
              · rintro ⟨⟨⟨h0, hb'⟩, hz, hu⟩, hn⟩
                exact ⟨⟨h0, by by_contra h; exact hn ⟨by linarith, hb'⟩⟩, hz, hu⟩
              · rintro ⟨⟨h0, ha'⟩, hz, hu⟩
                exact ⟨⟨⟨h0, by linarith⟩, hz, hu⟩, fun h => by linarith [h.1]⟩
            rw [hset] at this; linarith
          have hDinc : (net n).downTime j b - (net n).downTime j a = volume.real (Set.Ioc a b ∩ Dn) := by
            unfold Interruptions.downTime
            have hfin : volume (Set.Icc 0 b ∩ Dn) ≠ ⊤ :=
              ((measure_mono Set.inter_subset_left).trans_lt (measure_Icc_lt_top (a := (0:ℝ)) (b := b))).ne
            have := measureReal_inter_add_sdiff (μ := volume) (s := Set.Icc 0 b ∩ Dn) (t := Set.Ioc a b) measurableSet_Ioc hfin
            have hset1 : (Set.Icc 0 b ∩ Dn) ∩ Set.Ioc a b = Set.Ioc a b ∩ Dn := by
              ext s; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioc]
              constructor
              · rintro ⟨⟨_, hd⟩, h⟩; exact ⟨h, hd⟩
              · rintro ⟨h, hd⟩; exact ⟨⟨⟨by linarith [h.1], h.2⟩, hd⟩, h⟩
            have hset2 : (Set.Icc 0 b ∩ Dn) \ Set.Ioc a b = Set.Icc 0 a ∩ Dn := by
              ext s; simp only [Set.mem_diff, Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioc]
              constructor
              · rintro ⟨⟨⟨h0, hb'⟩, hd⟩, hn⟩
                exact ⟨⟨h0, by by_contra h; exact hn ⟨by linarith, hb'⟩⟩, hd⟩
              · rintro ⟨⟨h0, ha'⟩, hd⟩
                exact ⟨⟨⟨h0, by linarith⟩, hd⟩, fun h => by linarith [h.1]⟩
            rw [hset1, hset2] at this; linarith
          have hsplit : volume.real (Set.Ioc a b ∩ Dn) + volume.real (Set.Ioc a b \ Dn) = b - a := by
            rw [measureReal_inter_add_sdiff (hDmeas n j) measure_Ioc_lt_top.ne]
            rw [Real.volume_real_Ioc]; simp [hab]
          have hsub : {x | x ∈ Set.Icc 0 b ∧ 0 < Z n x j ∧ (net n).IsUp j x} ∩ Set.Ioc a b
              ⊆ Set.Ioc a b \ Dn := by
            rintro x ⟨⟨_, _, hu⟩, hx⟩; exact ⟨hx, hdisj n j x hu⟩
          have hle := measureReal_mono (μ := volume) hsub ((measure_mono Set.diff_subset).trans_lt (measure_Ioc_lt_top (a := a) (b := b))).ne
          have h1 : 0 ≤ volume.real
              ({x | x ∈ Set.Icc 0 b ∧ 0 < Z n x j ∧ (net n).IsUp j x} ∩ Set.Ioc a b) := measureReal_nonneg
          have h2 : 0 ≤ volume.real (Set.Ioc a b ∩ Dn) := measureReal_nonneg
          rw [hYdef, hYdef]
          refine ⟨⟨by linarith, by linarith⟩, ?_⟩
          intro hpos
          have heq : {x | x ∈ Set.Icc 0 b ∧ 0 < Z n x j ∧ (net n).IsUp j x} ∩ Set.Ioc a b
              = Set.Ioc a b \ Dn := by
            apply le_antisymm hsub
            rintro x ⟨hx, hxd⟩
            have hx0 : 0 ≤ x := by linarith [hx.1]
            refine ⟨⟨⟨hx0, hx.2⟩, hpos x hx, ?_⟩, hx⟩
            rcases hcover n j x hx0 with h | h
            · exact h
            · exact absurd h hxd
          rw [heq] at hBinc
          linarith
        have hrefl : ∀ n j τ, 0 ≤ τ → ∀ c, 0 ≤ c →
            (∀ s ∈ Set.Icc 0 τ, Z n s j = 0 → Y n j s ≤ c) → Y n j τ ≤ c := by
          intro n j τ hτ c hc hz
          have hZnn : ∀ s, 0 ≤ s → 0 ≤ Z n s j := fun s hs => (hsol n s hs j).1
          by_cases hne : ∃ s ∈ Set.Icc 0 τ, Z n s j = 0
          · set Zs := {s | s ∈ Set.Icc 0 τ ∧ Z n s j = 0} with hZs
            have hbdd : BddAbove Zs := ⟨τ, fun s hs => hs.1.2⟩
            have hZne : Zs.Nonempty := by obtain ⟨s, hs, h⟩ := hne; exact ⟨s, hs, h⟩
            set σ := sSup Zs
            have hστ : σ ≤ τ := csSup_le hZne (fun s hs => hs.1.2)
            have hσ0 : 0 ≤ σ := by
              obtain ⟨s, hs⟩ := hZne; exact hs.1.1.trans (le_csSup hbdd hs)
            have hflat : Y n j τ = Y n j σ := by
              refine ((hYinc n j σ τ hσ0 hστ).2) ?_
              intro s hs
              have h0 : 0 ≤ s := by linarith [hs.1]
              rcases (hZnn s h0).lt_or_eq with h | h
              · exact h
              · exfalso
                have : s ≤ σ := le_csSup hbdd ⟨⟨h0, hs.2⟩, h.symm⟩
                linarith [hs.1]
            rw [hflat]
            refine le_of_forall_pos_lt_add fun δ hδ => ?_
            obtain ⟨s, hs, hlt⟩ := exists_lt_of_lt_csSup hZne (show σ - δ < σ by linarith)
            have hsσ : s ≤ σ := le_csSup hbdd hs
            have := (hYinc n j s σ hs.1.1 hsσ).1.2
            have := hz s hs.1 hs.2
            linarith
          · push_neg at hne
            have := (hYinc n j 0 τ le_rfl hτ).2 (fun s hs => by
              have h0 : 0 ≤ s := le_of_lt hs.1
              exact lt_of_le_of_ne (hZnn s h0) (hne s ⟨h0, hs.2⟩).symm)
            rw [this, hY0]; exact hc
        have hPle1 : ∀ k j, P k j ≤ 1 := fun k j =>
          (Finset.single_le_sum (fun q _ => hPnn k q) (Finset.mem_univ j)).trans (hProw k)
        have hiter : ∀ i : ℕ, ∃ K, 0 ≤ K ∧ ∀ (w : Fin J → ℝ) (ε : ℝ), 0 ≤ ε →
            (∀ j, w j ≤ ε + ∑ k, P k j * w k) → ∀ j, w j ≤ ε * K + ∑ k, (P ^ i) k j * w k := by
          intro i
          induction i with
          | zero => exact ⟨0, le_rfl, fun w ε _ _ j => by simp [Matrix.one_apply]⟩
          | succ i ih =>
            obtain ⟨K, hK0, hK⟩ := ih
            refine ⟨1 + K * J, by positivity, fun w ε hε hw j => ?_⟩
            have h1 : ∑ k, P k j * w k ≤ ∑ k, P k j * (ε * K + ∑ l, (P ^ i) l k * w l) :=
              Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hK w ε hε hw k) (hPnn k j)
            have h2 : ∑ k, P k j * (ε * K + ∑ l, (P ^ i) l k * w l)
                = ε * K * ∑ k, P k j + ∑ l, (P ^ (i+1)) l j * w l := by
              simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, pow_succ, Matrix.mul_apply,
                Finset.sum_mul]
              congr 1
              · exact Finset.sum_congr rfl fun k _ => by ring
              · rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun l _ =>
                  Finset.sum_congr rfl fun k _ => by ring
            have h3 : ∑ k, P k j ≤ J := by
              calc ∑ k, P k j ≤ ∑ _k : Fin J, (1:ℝ) := Finset.sum_le_sum fun k _ => hPle1 k j
                _ = J := by simp
            have h4 : ε * K * ∑ k, P k j ≤ ε * K * J :=
              mul_le_mul_of_nonneg_left h3 (mul_nonneg hε hK0)
            have := hw j
            nlinarith
        have hmat : ∃ C, 0 ≤ C ∧ ∀ (w : Fin J → ℝ) (ε : ℝ), (∀ j, 0 ≤ w j) → 0 ≤ ε →
            (∀ j, w j ≤ ε + ∑ k, P k j * w k) → ∀ j, w j ≤ C * ε := by
          have hev : ∀ᶠ m in atTop, ∀ l j, |(P ^ m) l j| < 1 / (2 * (J + 1)) := by
            rw [eventually_all]; intro l; rw [eventually_all]; intro j
            have h := (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hPpow l) j)
            have hpos : (0:ℝ) < 1 / (2 * (J + 1)) := by positivity
            have := h.abs
            simpa using this.eventually (gt_mem_nhds (by simpa using hpos))
          obtain ⟨m, hm⟩ := hev.exists
          obtain ⟨K, hK0, hK⟩ := hiter m
          refine ⟨2 * J * K, by positivity, fun w ε hw0 hε hw j => ?_⟩
          have hb : ∀ j, w j ≤ ε * K + (∑ l, w l) / (2 * (J + 1)) := by
            intro j
            have := hK w ε hε hw j
            have h2 : ∑ k, (P ^ m) k j * w k ≤ ∑ k, 1 / (2 * (J + 1)) * w k :=
              Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right
                ((le_abs_self _).trans (hm k j).le) (hw0 k)
            rw [← Finset.mul_sum] at h2
            have : 1 / (2 * ((J:ℝ) + 1)) * ∑ k, w k = (∑ l, w l) / (2 * (J + 1)) := by ring
            linarith
          have hsum : ∑ l, w l ≤ J * (ε * K) + J * ((∑ l, w l) / (2 * (J + 1))) := by
            calc ∑ l, w l ≤ ∑ _l : Fin J, (ε * K + (∑ l, w l) / (2 * (J + 1))) :=
                  Finset.sum_le_sum fun l _ => hb l
              _ = _ := by simp [mul_add]
          have hS0 : 0 ≤ ∑ l, w l := Finset.sum_nonneg fun l _ => hw0 l
          have hJ : (J:ℝ) * ((∑ l, w l) / (2 * (J + 1))) ≤ (∑ l, w l) / 2 := by
            rw [mul_div_assoc']
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
          have hS : ∑ l, w l ≤ 2 * J * K * ε := by nlinarith
          have : w j ≤ ∑ l, w l := Finset.single_le_sum (fun l _ => hw0 l) (Finset.mem_univ j)
          linarith
        have H1 : ∀ K η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, Real.sqrt n * K ≤ η * n := by
          intro K η hη
          have h := (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (|K| / η)
          filter_upwards [h] with n hn
          simp only [Function.comp] at hn
          have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
          have h1 : |K| ≤ η * Real.sqrt n := by rw [div_le_iff₀ hη] at hn; linarith
          have h2 : Real.sqrt n * K ≤ Real.sqrt n * |K| :=
            mul_le_mul_of_nonneg_left (le_abs_self K) (Real.sqrt_nonneg _)
          nlinarith [Real.sqrt_nonneg (n:ℝ)]
        have H2 : ∀ (E : Type) [NormedAddCommGroup E] (f : ℕ → ℝ → E) (g : ℝ → E),
            UocTendsto f (fun t => if t < 0 then 0 else g t) → ContinuousOn g (Set.Ici 0) →
            ∀ T, ∃ K, ∀ᶠ n in atTop, ∀ t ∈ Set.Icc 0 T, ‖f n t‖ ≤ K := by
          intro E _ f g hf hg T
          obtain ⟨K0, hK0⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_bound_of_continuousOn
            (hg.mono Set.Icc_subset_Ici_self)
          refine ⟨K0 + 1, ?_⟩
          filter_upwards [hf T 1 one_pos] with n hn t ht
          have h1 := hn t ht
          rw [if_neg (not_lt.mpr ht.1)] at h1
          have h2 := hK0 t ht
          have := norm_le_norm_add_norm_sub' (f n t) (g t)
          linarith [norm_sub_rev (f n t) (g t)]
        have H3 : ∀ (θn : ℕ → Fin J → ℝ) (θ c : Fin J → ℝ),
            Tendsto (fun n : ℕ => Real.sqrt n • (θn n - θ)) atTop (𝓝 c) →
            ∀ η, 0 < η → ∀ᶠ n in atTop, ∀ j, |θn n j - θ j| ≤ η := by
          intro θn θ c hc η hη
          have hinv : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
            (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
          have hprod := hinv.smul hc
          rw [zero_smul] at hprod
          have hev : ∀ᶠ n : ℕ in atTop, (Real.sqrt n)⁻¹ • (Real.sqrt n • (θn n - θ)) = θn n - θ := by
            filter_upwards [eventually_ge_atTop 1] with n hn
            rw [smul_smul, inv_mul_cancel₀, one_smul]
            exact (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne'
          have h0 : Tendsto (fun n => θn n - θ) atTop (𝓝 0) := hprod.congr' hev
          rw [eventually_all]; intro j
          have := (tendsto_pi_nhds.mp h0 j)
          have := this.abs
          simp only [Pi.zero_apply, abs_zero, Pi.sub_apply] at this
          exact this.eventually (ge_mem_nhds hη)
        have hpat : ∀ (F : ℕ → ℝ → Fin J → ℝ) (θn : ℕ → Fin J → ℝ) (θ : Fin J → ℝ) (T K : ℝ), 0 ≤ T →
            (∀ᶠ n : ℕ in atTop, ∀ t ∈ Set.Icc 0 T, ∀ j,
              |(F n (n * t) j - θn n j * n * t) / Real.sqrt n| ≤ K) →
            (∀ η, 0 < η → ∀ᶠ n in atTop, ∀ j, |θn n j - θ j| ≤ η) →
            ∀ η, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ s ∈ Set.Icc 0 ((n:ℝ) * T), ∀ j,
              |F n s j - θ j * s| ≤ η * n := by
          intro F θn θ T K hT hK hθ η hη
          filter_upwards [hK, H1 K (η/2) (by positivity), hθ (η / (2 * (T + 1))) (by positivity),
            eventually_ge_atTop 1] with n hn h1 h3 hn1 s hs j
          have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
          have hsqpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
          have ht : s / n ∈ Set.Icc 0 T := ⟨div_nonneg hs.1 hnpos.le, by
            rw [div_le_iff₀ hnpos]; linarith [hs.2]⟩
          have h := hn (s / n) ht j
          have hns : (n:ℝ) * (s / n) = s := by field_simp
          rw [mul_assoc, hns, abs_div, abs_of_pos hsqpos, div_le_iff₀ hsqpos] at h
          have h4 : |(θn n j - θ j) * s| ≤ η / (2 * (T + 1)) * (n * T) := by
            rw [abs_mul, abs_of_nonneg hs.1]
            exact mul_le_mul (h3 j) hs.2 hs.1 (by positivity)
          have h5 : η / (2 * (T + 1)) * (n * T) ≤ η / 2 * n := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            nlinarith
          have : F n s j - θ j * s = (F n s j - θn n j * s) + (θn n j - θ j) * s := by ring
          rw [this]
          calc _ ≤ |F n s j - θn n j * s| + |(θn n j - θ j) * s| := abs_add_le _ _
            _ ≤ η * n := by linarith
        -- coordinates bounds for each family
        have hAK : ∀ T, ∃ K, ∀ᶠ n : ℕ in atTop, ∀ t ∈ Set.Icc 0 T, ∀ j,
            |(((net n).A (n * t) j : ℝ) - lamn n j * n * t) / Real.sqrt n| ≤ K := by
          intro T
          obtain ⟨K, hK⟩ := H2 _ _ L.A hAc hAreg T
          refine ⟨K, ?_⟩
          filter_upwards [hK] with n hn t ht j
          have := (norm_le_pi_norm _ j).trans (hn t ht)
          simpa [scaledPrimitives5, scaledPrimitives, not_lt.mpr ht.1, abs_div] using this
        have hSK : ∀ T, ∃ K, ∀ᶠ n : ℕ in atTop, ∀ t ∈ Set.Icc 0 T, ∀ j,
            |(((net n).S (n * t) j : ℝ) - mun n j * n * t) / Real.sqrt n| ≤ K := by
          intro T
          obtain ⟨K, hK⟩ := H2 _ _ L.S hSc hSreg T
          refine ⟨K, ?_⟩
          filter_upwards [hK] with n hn t ht j
          have := (norm_le_pi_norm _ j).trans (hn t ht)
          simpa [scaledPrimitives5, scaledPrimitives, not_lt.mpr ht.1, abs_div] using this
        have hDK : ∀ T, ∃ K, ∀ᶠ n : ℕ in atTop, ∀ t ∈ Set.Icc 0 T, ∀ j,
            |((net n).downTime j (n * t) - (1 - nun n j) * n * t) / Real.sqrt n| ≤ K := by
          intro T
          obtain ⟨K, hK⟩ := H2 _ _ L.D hDc hDreg T
          refine ⟨K, ?_⟩
          filter_upwards [hK] with n hn t ht j
          have := (norm_le_pi_norm _ j).trans (hn t ht)
          simpa [scaledPrimitives5, centredDown, not_lt.mpr ht.1, abs_div] using this
        have hRK : ∀ T, ∃ K, ∀ᶠ n : ℕ in atTop, ∀ t ∈ Set.Icc 0 T, ∀ k j,
            |((routingCount χ k j ⌊(n:ℝ) * t⌋₊ : ℝ) - P k j * n * t) / Real.sqrt n| ≤ K := by
          intro T
          obtain ⟨K, hK⟩ := H2 _ _ L.R hRc hRreg T
          refine ⟨K, ?_⟩
          filter_upwards [hK] with n hn t ht k j
          have := (norm_le_pi_norm ((scaledPrimitives5 χ (net n) (lamn n) (mun n) (nun n) P n).2.2.2.1 t k) j).trans ((norm_le_pi_norm _ k).trans (hn t ht))
          simpa [scaledPrimitives5, scaledPrimitives, not_lt.mpr ht.1, abs_div] using this
        have hnum : ∀ θ : Fin J → ℝ, ∀ η, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ j, |(1 - nun n j) - (1 - nu j)| ≤ η := by
          intro θ η hη
          filter_upwards [H3 nun nu cnu hnu η hη] with n hn j
          have := hn j; rw [show (1 - nun n j) - (1 - nu j) = -(nun n j - nu j) by ring, abs_neg]; exact this
        have hfluid : ∀ T, 0 ≤ T → ∀ δ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ s ∈ Set.Icc 0 ((n:ℝ) * T), ∀ j,
            |(Z n s j : ℝ) - mu j * Y n j s + ∑ k, P k j * mu k * Y n k s| ≤ δ * n ∧
            |Y n j s + B n s j - nu j * s| ≤ δ * n := by
          intro T hT δ hδ
          set Mμ := ∑ k, mu k with hMμ
          have hMμ0 : 0 ≤ Mμ := Finset.sum_nonneg fun k _ => (hmu0 k).le
          have hμle : ∀ k, mu k ≤ Mμ := fun k =>
            Finset.single_le_sum (f := mu) (fun l _ => (hmu0 l).le) (Finset.mem_univ k)
          set Q : ℝ := 3 + 2 * J + 2 * Mμ with hQ
          have hQ1 : 1 ≤ Q := by have : (0:ℝ) ≤ J := Nat.cast_nonneg J; linarith
          set η := δ / Q with hη
          have hη0 : 0 < η := div_pos hδ (by linarith)
          have hηQ : η * Q = δ := by rw [hη]; field_simp
          obtain ⟨KA, hKA⟩ := hAK T
          obtain ⟨KS, hKS⟩ := hSK T
          obtain ⟨KD, hKD⟩ := hDK T
          set T2 := Mμ * T + 1 with hT2
          have hT20 : 0 ≤ T2 := by positivity
          obtain ⟨KR, hKR⟩ := hRK T2
          have eA := hpat (fun n s j => ((net n).A s j : ℝ)) lamn lam T KA hT hKA
            (H3 lamn lam clam hlam) η hη0
          have eS := hpat (fun n s j => ((net n).S s j : ℝ)) mun mu T KS hT hKS
            (H3 mun mu cmu hmu) η hη0
          have eS1 := hpat (fun n s j => ((net n).S s j : ℝ)) mun mu T KS hT hKS
            (H3 mun mu cmu hmu) 1 one_pos
          have eD := hpat (fun n s j => (net n).downTime j s) (fun n j => 1 - nun n j) (fun j => 1 - nu j)
            T KD hT hKD (hnum nu) η hη0
          have eR : ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, (m:ℝ) ≤ n * T2 → ∀ k j,
              |(routingCount χ k j m : ℝ) - P k j * m| ≤ η * n := by
            filter_upwards [hKR, H1 KR η hη0, eventually_ge_atTop 1] with n hn h1 hn1 m hm k j
            have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
            have hsqpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
            have ht : (m:ℝ) / n ∈ Set.Icc 0 T2 := ⟨div_nonneg (Nat.cast_nonneg m) hnpos.le, by
              rw [div_le_iff₀ hnpos]; linarith⟩
            have h := hn _ ht k j
            have hns : (n:ℝ) * ((m:ℝ) / n) = m := by field_simp
            rw [mul_assoc, hns, Nat.floor_natCast, abs_div, abs_of_pos hsqpos, div_le_iff₀ hsqpos] at h
            linarith
          have eZ0 : ∀ᶠ n : ℕ in atTop, ∀ j, |((net n).Z0 j : ℝ)| ≤ η * n := by
            rw [eventually_all]; intro j
            have hc := tendsto_pi_nhds.mp hZ0c j
            have hb := hc.abs.eventually (ge_mem_nhds (show |L.toPrim5.1 j| < |L.Z0 j| + 1 by
              simp [LimitData5.toPrim5]))
            filter_upwards [hb, H1 (|L.Z0 j| + 1) η hη0, eventually_ge_atTop 1] with n hn h1 hn1
            have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
            have hsqpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
            simp only [scaledPrimitives5, scaledPrimitives] at hn
            rw [abs_div, abs_of_pos hsqpos, div_le_iff₀ hsqpos] at hn
            linarith
          filter_upwards [eA, eS, eS1, eD, eR, eZ0, eventually_ge_atTop 1] with
            n hA hS hS1 hD hR hZ0 hn1 s hs j
          have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
          have hs0 := hs.1
          have hb : ∀ k, B n s k ∈ Set.Icc 0 ((n:ℝ) * T) := fun k =>
            ⟨(hBle n k s hs0).1, (hBle n k s hs0).2.trans hs.2⟩
          have hSk : ∀ k, |((net n).S (B n s k) k : ℝ) - mu k * B n s k| ≤ η * n := fun k =>
            hS _ (hb k) k
          have hmk : ∀ k, ((net n).S (B n s k) k : ℝ) ≤ n * T2 := by
            intro k
            have h1 := (abs_le.mp (hS1 _ (hb k) k)).2
            have h2 : mu k * B n s k ≤ Mμ * (n * T) :=
              mul_le_mul (hμle k) (hb k).2 (hb k).1 hMμ0
            rw [hT2]; nlinarith
          have hRk : ∀ k, |(routingCount χ k j ((net n).S (B n s k) k) : ℝ)
              - P k j * ((net n).S (B n s k) k : ℝ)| ≤ η * n := fun k => by
            have := hR _ (hmk k) k j
            exact_mod_cast this
          have hDk : ∀ k, |(net n).downTime k s - (1 - nu k) * s| ≤ η * n := fun k => hD s hs k
          have hAj : |((net n).A s j : ℝ) - lam j * s| ≤ η * n := hA s hs j
          have hZ0j := hZ0 j
          have hZr : (Z n s j : ℝ) = ((net n).Z0 j : ℝ) + ((net n).A s j : ℝ)
              + ∑ k, (routingCount χ k j ((net n).S (B n s k) k) : ℝ) - ((net n).S (B n s j) j : ℝ) := by
            rw [(hsol n s hs0 j).2.1]; push_cast; ring
          have hsum : ∑ k, ((routingCount χ k j ((net n).S (B n s k) k) : ℝ)
                - P k j * ((net n).S (B n s k) k : ℝ))
              + ∑ k, P k j * (((net n).S (B n s k) k : ℝ) - mu k * B n s k)
              - ∑ k, P k j * mu k * ((net n).downTime k s - (1 - nu k) * s)
              = ∑ k, (routingCount χ k j ((net n).S (B n s k) k) : ℝ)
                + ∑ k, P k j * mu k * Y n k s - (∑ k, P k j * mu k * nu k) * s := by
            simp only [hYdef]
            rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
              ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun k _ => by ring
          have hl : lam j * s = mu j * nu j * s - (∑ k, P k j * mu k * nu k) * s := by
            rw [← hbal j]; ring
          have hid : (Z n s j : ℝ) - mu j * Y n j s + ∑ k, P k j * mu k * Y n k s
              = ((net n).Z0 j : ℝ) + (((net n).A s j : ℝ) - lam j * s)
                + (∑ k, ((routingCount χ k j ((net n).S (B n s k) k) : ℝ)
                  - P k j * ((net n).S (B n s k) k : ℝ))
                + ∑ k, P k j * (((net n).S (B n s k) k : ℝ) - mu k * B n s k)
                - ∑ k, P k j * mu k * ((net n).downTime k s - (1 - nu k) * s))
                - (((net n).S (B n s j) j : ℝ) - mu j * B n s j)
                + mu j * ((net n).downTime j s - (1 - nu j) * s) := by
            rw [hsum, hZr, hYdef n j s]; linarith
          have b1 : |∑ k, ((routingCount χ k j ((net n).S (B n s k) k) : ℝ)
                  - P k j * ((net n).S (B n s k) k : ℝ))| ≤ J * (η * n) := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
            calc _ ≤ ∑ _k : Fin J, η * n := Finset.sum_le_sum fun k _ => hRk k
              _ = _ := by simp
          have b2 : |∑ k, P k j * (((net n).S (B n s k) k : ℝ) - mu k * B n s k)| ≤ J * (η * n) := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
            calc _ ≤ ∑ _k : Fin J, η * n := Finset.sum_le_sum fun k _ => by
                  rw [abs_mul, abs_of_nonneg (hPnn k j)]
                  calc P k j * _ ≤ 1 * (η * n) :=
                        mul_le_mul (hPle1 k j) (hSk k) (abs_nonneg _) zero_le_one
                    _ = η * n := one_mul _
              _ = _ := by simp
          have b3 : |∑ k, P k j * mu k * ((net n).downTime k s - (1 - nu k) * s)| ≤ Mμ * (η * n) := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
            calc _ ≤ ∑ k, mu k * (η * n) := Finset.sum_le_sum fun k _ => by
                  rw [abs_mul, abs_mul, abs_of_nonneg (hPnn k j), abs_of_pos (hmu0 k)]
                  calc P k j * mu k * _ ≤ (1 * mu k) * (η * n) :=
                        mul_le_mul (mul_le_mul_of_nonneg_right (hPle1 k j) (hmu0 k).le) (hDk k)
                          (abs_nonneg _) (by linarith [hmu0 k])
                    _ = mu k * (η * n) := by ring
              _ = _ := by rw [← Finset.sum_mul]
          have b4 : |mu j * ((net n).downTime j s - (1 - nu j) * s)| ≤ Mμ * (η * n) := by
            rw [abs_mul, abs_of_pos (hmu0 j)]
            exact mul_le_mul (hμle j) (hDk j) (abs_nonneg _) hMμ0
          have b5 := hSk j
          have hηn : η * n * Q = δ * n := by rw [← hηQ]; ring
          have hexp : δ * n = 3 * (η * n) + 2 * (J * (η * n)) + 2 * (Mμ * (η * n)) := by
            rw [← hηn, hQ]; ring
          constructor
          · rw [hid]
            rw [abs_le] at b1 b2 b3 b4 b5 hAj hZ0j ⊢
            constructor <;> linarith
          · have : Y n j s + B n s j - nu j * s = -((net n).downTime j s - (1 - nu j) * s) := by
              rw [hYdef]; ring
            rw [this, abs_neg]
            have := hDk j
            have h1 : 0 ≤ (J:ℝ) * (η * n) := by positivity
            have h2 : 0 ≤ Mμ * (η * n) := mul_nonneg hMμ0 (by positivity)
            have h0 : 0 ≤ η * n := by positivity
            linarith
        intro T ε hε
        set T' := max T 0 with hT'
        have hT'0 : 0 ≤ T' := le_max_right _ _
        obtain ⟨C, hC0, hC⟩ := hmat
        set Mi : ℝ := 1 + ∑ j, 1 / mu j with hMi
        have hMi : ∀ j, 1 / mu j ≤ Mi := by
          intro j
          have := Finset.single_le_sum (f := fun j => 1 / mu j) (fun l _ => (one_div_pos.mpr (hmu0 l)).le)
            (Finset.mem_univ j)
          linarith
        have hMi0 : 0 ≤ Mi := by
          have : 0 ≤ ∑ j, 1 / mu j := Finset.sum_nonneg fun l _ => (one_div_pos.mpr (hmu0 l)).le
          linarith
        set δ := ε / (2 * (1 + C * Mi)) with hδ
        have hden : 0 < 2 * (1 + C * Mi) := by positivity
        have hδ0 : 0 < δ := div_pos hε hden
        filter_upwards [hfluid T' hT'0 δ hδ0, eventually_ge_atTop 1] with n hn hn1
        intro t ht
        have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
        set s := (n:ℝ) * t with hs
        have hs0 : 0 ≤ s := mul_nonneg hnpos.le ht.1
        have hsT : s ≤ n * T' := mul_le_mul_of_nonneg_left (ht.2.trans (le_max_left _ _)) hnpos.le
        have hYmono : ∀ k a, 0 ≤ a → a ≤ s → 0 ≤ Y n k a ∧ Y n k a ≤ Y n k s := by
          intro k a ha has
          have h1 := (hYinc n k 0 a le_rfl ha).1.1
          have h2 := (hYinc n k a s ha has).1.1
          rw [hY0] at h1; constructor <;> linarith
        have hw0 : ∀ k, 0 ≤ mu k * Y n k s := fun k =>
          mul_nonneg (hmu0 k).le (hYmono k s hs0 le_rfl).1
        have hw : ∀ j, mu j * Y n j s ≤ δ * n + ∑ k, P k j * (mu k * Y n k s) := by
          intro j
          have hc0 : 0 ≤ (δ * n + ∑ k, P k j * (mu k * Y n k s)) / mu j := by
            apply div_nonneg _ (hmu0 j).le
            have := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => mul_nonneg (hPnn k j) (hw0 k)
            positivity
          have := hrefl n j s hs0 _ hc0 (by
            intro s' hs' hz
            rw [le_div_iff₀ (hmu0 j)]
            have hf := (hn s' ⟨hs'.1, hs'.2.trans hsT⟩ j).1
            rw [hz] at hf
            have hsum : ∑ k, P k j * mu k * Y n k s' ≤ ∑ k, P k j * (mu k * Y n k s) :=
              Finset.sum_le_sum fun k _ => by
                rw [← mul_assoc]
                exact mul_le_mul_of_nonneg_left (hYmono k s' hs'.1 hs'.2).2
                  (mul_nonneg (hPnn k j) (hmu0 k).le)
            have := (abs_le.mp hf).1
            push_cast at this
            linarith)
          rw [le_div_iff₀ (hmu0 j)] at this
          linarith
        have hwC := hC (fun k => mu k * Y n k s) (δ * n) hw0 (by positivity) hw
        rw [pi_norm_lt_iff hε]
        intro j
        rw [Real.norm_eq_abs]
        simp only [Pi.sub_apply]
        have hYj : Y n j s ≤ C * (δ * n) * Mi := by
          have h1 := hwC j
          have h2 : Y n j s = (mu j * Y n j s) * (1 / mu j) := by
            field_simp [(hmu0 j).ne']
          rw [h2]
          calc mu j * Y n j s * (1 / mu j) ≤ C * (δ * n) * (1 / mu j) :=
                mul_le_mul_of_nonneg_right h1 (one_div_pos.mpr (hmu0 j)).le
            _ ≤ C * (δ * n) * Mi := mul_le_mul_of_nonneg_left (hMi j) (by positivity)
        have hYj0 := (hYmono j s hs0 le_rfl).1
        have hU := (hn s ⟨hs0, hsT⟩ j).2
        have hkey : |B n s j - nu j * s| ≤ δ * n * (1 + C * Mi) := by
          have he : δ * n * (1 + C * Mi) = δ * n + C * (δ * n) * Mi := by ring
          rw [he]
          rw [abs_le] at hU ⊢; constructor <;> linarith
        have heq : B n s j / n - nu j * t = (B n s j - nu j * s) / n := by
          rw [hs]; field_simp
        rw [heq, abs_div, abs_of_pos hnpos, div_lt_iff₀ hnpos]
        have : δ * n * (1 + C * Mi) = ε / 2 * n := by
          rw [hδ]; field_simp
        have := mul_pos hε hnpos
        linarith
