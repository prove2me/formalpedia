-- Prove2me | solution 1 for EquilibriumExperiment.Gradient.Supplement.theorem_9
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:49:28.518301+00:00
-- url     : https://prove2.me/submissions/db22a64a-21a3-43c7-b289-e71dea07a816

import Mathlib
import Definitions.Def_EquilibriumExperiment_Gradient_Supplement_Learning
import Definitions.Def_EquilibriumExperiment_Gradient_Supplement_PerturbedUtility

open MeasureTheory ProbabilityTheory Filter Topology

open EquilibriumExperiment
open EquilibriumExperiment.Gradient
open EquilibriumExperiment.Gradient.Supplement

theorem solution {A B : Type} [Fintype A] [Nonempty A] [MeasurableSpace B]
    (E : ContextFamily A B) (hE : ∀ a, (E.market a).Standing)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : lo ≤ hi)
    (hpos : ∀ a, ∀ p ∈ Set.Icc lo hi,
      0 < ∫ b, (E.market a).f b (p * (E.market a).omegaSup) ∂(E.market a).β) :
    ∃ C : ℝ, 0 < C ∧ ∃ radius : ℝ, 0 < radius ∧ radius < lo ∧
      ∀ T : ℕ, 1 ≤ T → ∀ states : Fin T → A, ∀ payments : Fin T → ℝ,
      (∀ t, payments t ∈ Set.Icc lo hi) → ∀ ζ ∈ Set.Ico (0 : ℝ) radius,
      (∑ t : Fin T, ((E.market (states t)).u (payments t) -
        uPert (E.market (states t)) (payments t) ζ)) / T ≤ C * ζ ^ 2 := by
          have hPL : ∀ (p ζ : ℝ) (g : ℝ → ℝ), ∫ x, g x ∂(perturbLaw p ζ) = (g (p + ζ) + g (p - ζ)) / 2 := by
            intro p ζ g
            unfold perturbLaw
            rw [integral_smul_measure, integral_add_measure (integrable_dirac (by simp))
              (integrable_dirac (by simp)), integral_dirac, integral_dirac]
            simp; ring
          have alg : ∀ (a c qa qc Ra Rc p ζ φp φm X Y Z e L0 Hi : ℝ), 0 ≤ a → a ≤ 1 → 0 ≤ qc → qc ≤ 1 →
              0 ≤ p → p ≤ Hi → 0 ≤ X → 0 ≤ Y → 0 ≤ Z →
              |Ra - Rc| ≤ X * |a - c| → |Rc| ≤ Y → |qa - qc| ≤ Z * |a - c| → |a - c| ≤ e →
              c = (φp + φm) / 2 → qc * ζ * (φp - φm) / 2 ≤ ζ ^ 2 * L0 →
              (Ra - p * qa) * a - (Rc * c - qc * (((p + ζ) * φp + (p - ζ) * φm) / 2)) ≤
                (X + Y + Hi * (Z + 1)) * e + ζ ^ 2 * L0 := by
            intro a c qa qc Ra Rc p ζ φp φm X Y Z e L0 Hi ha0 ha1 hq0 hq1 hp0 hpH hX0 hY0 hZ0 hX hY hZ hae hc hT
            have hac0 : 0 ≤ |a - c| := abs_nonneg _
            have he0 : 0 ≤ e := hac0.trans hae
            have hH0 : 0 ≤ Hi := hp0.trans hpH
            have h1 : (Ra - Rc) * a ≤ X * e := by
              have i1 : (Ra - Rc) * a ≤ |Ra - Rc| * a := mul_le_mul_of_nonneg_right (le_abs_self _) ha0
              have i2 : |Ra - Rc| * a ≤ |Ra - Rc| * 1 := mul_le_mul_of_nonneg_left ha1 (abs_nonneg _)
              have i3 : X * |a - c| ≤ X * e := mul_le_mul_of_nonneg_left hae hX0
              linarith only [i1, i2, i3, hX]
            have h2 : Rc * (a - c) ≤ Y * e := by
              have i1 : Rc * (a - c) ≤ |Rc * (a - c)| := le_abs_self _
              rw [abs_mul] at i1
              have i2 : |Rc| * |a - c| ≤ Y * e := mul_le_mul hY hae hac0 hY0
              linarith only [i1, i2]
            have h3 : -(p * ((qa - qc) * a)) ≤ Hi * (Z * e) := by
              have i1 : -(p * ((qa - qc) * a)) ≤ |p * ((qa - qc) * a)| := neg_le_abs _
              rw [abs_mul, abs_mul, abs_of_nonneg hp0, abs_of_nonneg ha0] at i1
              have i2 : |qa - qc| * a ≤ (Z * e) * 1 :=
                mul_le_mul (hZ.trans (mul_le_mul_of_nonneg_left hae hZ0)) ha1 ha0 (mul_nonneg hZ0 he0)
              have i3 : p * (|qa - qc| * a) ≤ Hi * ((Z * e) * 1) :=
                mul_le_mul hpH i2 (mul_nonneg (abs_nonneg _) ha0) hH0
              linarith only [i1, i3]
            have h4 : -(p * (qc * (a - c))) ≤ Hi * e := by
              have i1 : -(p * (qc * (a - c))) ≤ |p * (qc * (a - c))| := neg_le_abs _
              rw [abs_mul, abs_mul, abs_of_nonneg hp0, abs_of_nonneg hq0] at i1
              have i2 : qc * |a - c| ≤ 1 * e := mul_le_mul hq1 hae hac0 zero_le_one
              have i3 : p * (qc * |a - c|) ≤ Hi * (1 * e) := mul_le_mul hpH i2 (mul_nonneg hq0 hac0) hH0
              linarith only [i1, i3]
            have hid : (Ra - p * qa) * a - (Rc * c - qc * (((p + ζ) * φp + (p - ζ) * φm) / 2)) =
                (Ra - Rc) * a + Rc * (a - c) + -(p * ((qa - qc) * a)) + -(p * (qc * (a - c))) +
                  qc * ζ * (φp - φm) / 2 := by
              subst hc; ring
            rw [hid]
            linarith only [h1, h2, h3, h4, hT]
          have key : ∀ M : Market B, M.Standing →
              (∀ p ∈ Set.Icc lo hi, 0 < ∫ b, M.f b (p * M.omegaSup) ∂M.β) →
              ∃ C : ℝ, 0 < C ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ < lo ∧ ∀ p ∈ Set.Icc lo hi, ∀ ζ ∈ Set.Ico (0:ℝ) ρ,
                M.u p - uPert M p ζ ≤ C * ζ ^ 2 := by
            intro M hM hMpos
            obtain ⟨hd, hF, hF2, h31, h32, hβ, hω, hΩ1, hΩ2, hl1, hl2, hΩl, hΩm, hf01, hfmono, hfd,
              ⟨K1, hK1⟩, hfmeas, hf'meas, hr0, hrsmooth, hrd⟩ := hM
            obtain ⟨hω01, hωsmooth, hωconc, hωmono, hω0, hωtop, hωd⟩ := hω
            obtain ⟨K, hK0, hK⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ b x, 0 ≤ x → |M.f'' b x| ≤ K :=
              ⟨max K1 0, le_max_right _ _, fun b x hx => le_trans (hK1 b x hx) (le_max_left _ _)⟩
            -- convexity
            have hconv : ∀ b, ConvexOn ℝ (Set.Ici 0) (fun x => M.f b x + K / 2 * x ^ 2) := by
              intro b
              refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici 0)
                (f' := fun x => M.f' b x + K * x) (f'' := fun x => M.f'' b x + K) ?_ ?_ ?_ ?_
              · intro x hx
                exact ((hfd b x hx).1.continuousWithinAt).add (by fun_prop)
              · intro x hx
                rw [interior_Ici] at hx ⊢
                have h1 := ((hfd b x (le_of_lt hx)).1).mono Set.Ioi_subset_Ici_self
                have h2 : HasDerivWithinAt (fun x : ℝ => K / 2 * x ^ 2) (K * x) (Set.Ioi 0) x := by
                  have := ((hasDerivAt_pow 2 x).const_mul (K / 2)).hasDerivWithinAt (s := Set.Ioi 0)
                  exact this.congr_deriv (by norm_num; ring)
                exact h1.add h2
              · intro x hx
                rw [interior_Ici] at hx ⊢
                have h1 := ((hfd b x (le_of_lt hx)).2).mono Set.Ioi_subset_Ici_self
                have h2 : HasDerivWithinAt (fun x : ℝ => K * x) K (Set.Ioi 0) x := by
                  have := ((hasDerivAt_id x).const_mul K).hasDerivWithinAt (s := Set.Ioi 0)
                  simpa using this
                exact h1.add h2
              · intro x hx
                rw [interior_Ici] at hx
                have k1 := hK b x (le_of_lt hx)
                have k2 := neg_abs_le (M.f'' b x)
                linarith only [k1, k2]
            have hconc : ∀ b, ConcaveOn ℝ (Set.Ici 0) (fun x => M.f b x - K / 2 * x ^ 2) := by
              intro b
              refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ici 0)
                (f' := fun x => M.f' b x - K * x) (f'' := fun x => M.f'' b x - K) ?_ ?_ ?_ ?_
              · intro x hx
                exact ((hfd b x hx).1.continuousWithinAt).sub (by fun_prop)
              · intro x hx
                rw [interior_Ici] at hx ⊢
                have h1 := ((hfd b x (le_of_lt hx)).1).mono Set.Ioi_subset_Ici_self
                have h2 : HasDerivWithinAt (fun x : ℝ => K / 2 * x ^ 2) (K * x) (Set.Ioi 0) x := by
                  have := ((hasDerivAt_pow 2 x).const_mul (K / 2)).hasDerivWithinAt (s := Set.Ioi 0)
                  exact this.congr_deriv (by norm_num; ring)
                exact h1.sub h2
              · intro x hx
                rw [interior_Ici] at hx ⊢
                have h1 := ((hfd b x (le_of_lt hx)).2).mono Set.Ioi_subset_Ici_self
                have h2 : HasDerivWithinAt (fun x : ℝ => K * x) K (Set.Ioi 0) x := by
                  have := ((hasDerivAt_id x).const_mul K).hasDerivWithinAt (s := Set.Ioi 0)
                  simpa using this
                exact h1.sub h2
              · intro x hx
                rw [interior_Ici] at hx
                have k1 := hK b x (le_of_lt hx)
                have k2 := le_abs_self (M.f'' b x)
                linarith only [k1, k2]
            -- second difference bound
            have hT1 : ∀ b x h, 0 ≤ h → h ≤ x →
                |(M.f b (x + h) + M.f b (x - h)) / 2 - M.f b x| ≤ K / 2 * h ^ 2 := by
              intro b x h hh hhx
              have m1 : x - h ∈ Set.Ici (0:ℝ) := Set.mem_Ici.2 (by linarith only [hh, hhx])
              have m2 : x + h ∈ Set.Ici (0:ℝ) := Set.mem_Ici.2 (by linarith only [hh, hhx])
              have e : (1/2:ℝ) • (x - h) + (1/2:ℝ) • (x + h) = x := by rw [smul_eq_mul, smul_eq_mul]; ring
              have c1 := (hconv b).2 m1 m2 (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
                (by norm_num)
              have c2 := (hconc b).2 m1 m2 (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
                (by norm_num)
              rw [e] at c1 c2
              simp only [smul_eq_mul] at c1 c2
              rw [abs_le]; constructor <;> linarith only [c1, c2]
            have hT2 : ∀ b x h, 0 ≤ h → h ≤ x →
                M.f b (x + h) - M.f b (x - h) ≤ 2 * h * (1 + K * (2 * h + 1) / 2) := by
              intro b x h hh hhx
              rcases eq_or_lt_of_le hh with h0 | hpos'
              · subst h0; simp
              have m1 : x - h ∈ Set.Ici (0:ℝ) := Set.mem_Ici.2 (by linarith only [hh, hhx])
              have m3 : x + h + 1 ∈ Set.Ici (0:ℝ) := Set.mem_Ici.2 (by linarith only [hh, hhx])
              have s := (hconv b).slope_mono_adjacent m1 m3 (by linarith only [hpos'] : x - h < x + h)
                (by linarith only : x + h < x + h + 1)
              have e1 : x + h - (x - h) = 2 * h := by ring
              have e2 : x + h + 1 - (x + h) = 1 := by ring
              rw [e1, e2, div_one, div_le_iff₀ (by linarith only [hpos'])] at s
              have a1 := (hf01 b (x + h + 1) (by linarith only [hh, hhx])).2
              have a2 := (hf01 b (x + h) (by linarith only [hh, hhx])).1
              have a3 : (M.f b (x + h + 1) - M.f b (x + h)) * (2 * h) ≤ 1 * (2 * h) :=
                mul_le_mul_of_nonneg_right (by linarith only [a1, a2]) (by linarith only [hh])
              linarith only [s, a3]
            have := hβ
            obtain ⟨φ, hφ⟩ : ∃ φ : ℝ → ℝ, ∀ x, φ x = ∫ b, M.f b x ∂M.β := ⟨_, fun x => rfl⟩
            have hint : ∀ x, 0 ≤ x → Integrable (fun b => M.f b x) M.β := by
              intro x hx
              refine Integrable.of_bound (C := 1) ?_ ?_
              · exact (hfmeas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
              · refine Filter.Eventually.of_forall (fun b => ?_)
                have := hf01 b x hx
                rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith only [this.1, this.2]
            have hφ01 : ∀ x, 0 ≤ x → 0 ≤ φ x ∧ φ x ≤ 1 := by
              intro x hx
              rw [hφ]
              constructor
              · exact integral_nonneg (fun b => (hf01 b x hx).1)
              · calc ∫ b, M.f b x ∂M.β ≤ ∫ b, (1:ℝ) ∂M.β :=
                      integral_mono (hint x hx) (integrable_const _) (fun b => (hf01 b x hx).2)
                  _ = 1 := by simp
            have hφmono : ∀ x y, 0 ≤ x → x ≤ y → φ x ≤ φ y := by
              intro x y hx hxy
              rw [hφ, hφ]
              exact integral_mono (hint x hx) (hint y (le_trans hx hxy))
                (fun b => hfmono b (Set.mem_Ici.2 hx) (Set.mem_Ici.2 (le_trans hx hxy)) hxy)
            have hφcont : ContinuousOn φ (Set.Ici 0) := by
              have : φ = fun x => ∫ b, M.f b x ∂M.β := funext hφ
              rw [this]
              refine continuousOn_of_dominated (bound := fun _ => 1) ?_ ?_ (integrable_const _) ?_
              · intro x hx
                exact (hint x hx).aestronglyMeasurable
              · intro x hx
                refine Filter.Eventually.of_forall (fun b => ?_)
                have := hf01 b x hx
                rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith only [this.1, this.2]
              · refine Filter.Eventually.of_forall (fun b => ?_)
                intro x hx
                exact (hfd b x hx).1.continuousWithinAt
            -- omegaSup facts
            have hne : (M.ω '' Set.Ici 0).Nonempty := ⟨M.ω 0, 0, Set.mem_Ici.2 le_rfl, rfl⟩
            have hωbdd : BddAbove (M.ω '' Set.Ici 0) := ⟨1, by
              rintro _ ⟨y, hy, rfl⟩; exact (hω01 y hy).2⟩
            have hωle : ∀ y, 0 ≤ y → M.ω y ≤ M.omegaSup := fun y hy =>
              le_csSup hωbdd ⟨y, hy, rfl⟩
            have hωS0 : 0 ≤ M.omegaSup := le_trans (hω01 0 le_rfl).1 (hωle 0 le_rfl)
            have hωS1 : M.omegaSup ≤ 1 := csSup_le hne (by
              rintro _ ⟨y, hy, rfl⟩; exact (hω01 y hy).2)
            have hωapprox : ∀ ε > 0, ∃ y, 0 ≤ y ∧ M.omegaSup - ε < M.ω y := by
              intro ε hε
              obtain ⟨_, ⟨y, hy, rfl⟩, h⟩ := exists_lt_of_lt_csSup hne
                (sub_lt_self _ hε)
              exact ⟨y, hy, h⟩
            -- positivity margin
            set x0 := lo * M.omegaSup with hx0
            have hx00 : 0 ≤ x0 := mul_nonneg hlo.le hωS0
            have hφx0 : 0 < φ x0 := by rw [hφ]; exact hMpos lo ⟨le_rfl, hhi⟩
            obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.1 (hφcont x0 hx00) (φ x0 / 2)
              (half_pos hφx0)
            have hmarg : ∀ x, 0 ≤ x → x0 - δ / 2 ≤ x → φ x0 / 2 < φ x := by
              intro x hx hxx
              rcases le_or_gt x0 x with h | h
              · linarith only [hφmono x0 x hx00 h, hφx0]
              · have := hδc (x := x) hx (by
                  rw [Real.dist_eq, abs_lt]; constructor <;> linarith only [h, hxx, hδ])
                rw [Real.dist_eq, abs_lt] at this
                linarith only [this.1]
            obtain ⟨y, hy0, hy⟩ := hωapprox (δ / (4 * lo)) (by positivity)
            set Y := max y 1 with hY
            have hY1 : 1 ≤ Y := le_max_right _ _
            have hωY : M.omegaSup - δ / (4 * lo) < M.ω Y :=
              lt_of_lt_of_le hy (hωmono (Set.mem_Ici.2 hy0) (Set.mem_Ici.2 (by linarith only [hY1]))
                (le_max_left _ _))
            set μ0 := min 1 (M.d / Y) with hμ0
            have hμ00 : 0 < μ0 := lt_min one_pos (div_pos hd (by linarith only [hY1]))
            set ρ := min (lo / 2) (δ / 4) with hρ
            have hρ0 : 0 < ρ := lt_min (by linarith only [hlo]) (by linarith only [hδ])
            have hρlo : ρ < lo := lt_of_le_of_lt (min_le_left _ _) (by linarith only [hlo])
            obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℝ → ℝ → ℝ → ℝ, ∀ p ζ μ,
                Ψ p ζ μ = (φ ((p + ζ) * M.ω (M.d / μ)) + φ ((p - ζ) * M.ω (M.d / μ))) / 2 :=
              ⟨_, fun _ _ _ => rfl⟩
            have hdμ : ∀ μ, 0 < μ → μ ≤ 1 → M.d ≤ M.d / μ := by
              intro μ h1 h2; rw [le_div_iff₀ h1]; exact mul_le_of_le_one_right hd.le h2
            have hq0 : ∀ μ, 0 < μ → μ ≤ 1 → 0 ≤ M.ω (M.d / μ) ∧ M.ω (M.d / μ) ≤ 1 := by
              intro μ h1 h2; exact hω01 _ (by positivity)
            have hsmall : ∀ p ∈ Set.Icc lo hi, ∀ ζ ∈ Set.Ico (0:ℝ) ρ, ∀ μ, 0 < μ → μ ≤ μ0 →
                φ x0 / 2 < Ψ p ζ μ := by
              intro p hp ζ hζ μ h1 h2
              have hμY : Y ≤ M.d / μ := by
                rw [le_div_iff₀ h1]
                have : μ ≤ M.d / Y := le_trans h2 (min_le_right _ _)
                rw [le_div_iff₀ (by linarith only [hY1])] at this; linarith only [this]
              have hωμ : M.ω Y ≤ M.ω (M.d / μ) :=
                hωmono (Set.mem_Ici.2 (by linarith only [hY1])) (Set.mem_Ici.2 (by linarith only [hY1, hμY])) hμY
              have hq := hq0 μ h1 (le_trans h2 (min_le_left _ _))
              have hζρ : ζ < ρ := hζ.2
              have hρ1 : ρ ≤ lo / 2 := min_le_left _ _
              have hρ2 : ρ ≤ δ / 4 := min_le_right _ _
              have he : lo * (δ / (4 * lo)) = δ / 4 := by field_simp
              have hA : x0 - δ / 2 ≤ (p - ζ) * M.ω (M.d / μ) := by
                have i1 : (lo - ρ) * M.ω (M.d / μ) ≤ (p - ζ) * M.ω (M.d / μ) :=
                  mul_le_mul_of_nonneg_right (by linarith only [hp.1, hζρ]) hq.1
                have i2 : (lo - ρ) * (M.omegaSup - δ / (4 * lo)) ≤ (lo - ρ) * M.ω (M.d / μ) :=
                  mul_le_mul_of_nonneg_left (by linarith only [hωY, hωμ]) (by linarith only [hρ1, hlo])
                have i3 : 0 ≤ ρ * (δ / (4 * lo)) :=
                  mul_nonneg (by linarith only [hρ1, hζρ, hζ.1]) (div_nonneg hδ.le (by linarith only [hlo]))
                have i4 : ρ * M.omegaSup ≤ ρ * 1 :=
                  mul_le_mul_of_nonneg_left hωS1 (by linarith only [hζρ, hζ.1])
                linarith only [i1, i2, i3, i4, he, hρ2, hx0]
              have hB0 : 0 ≤ (p - ζ) * M.ω (M.d / μ) :=
                mul_nonneg (by linarith only [hp.1, hζρ, hρ1, hlo]) hq.1
              have h3 := hmarg _ hB0 hA
              have h4 := hφmono _ ((p + ζ) * M.ω (M.d / μ)) hB0
                (mul_le_mul_of_nonneg_right (by linarith only [hζ.1]) hq.1)
              rw [hΨ]; linarith only [h3, h4]
            set m := min μ0 (φ x0 / 2) with hm
            have hm0 : 0 < m := lt_min hμ00 (by linarith only [hφx0])
            have hlow : ∀ p ∈ Set.Icc lo hi, ∀ ζ ∈ Set.Ico (0:ℝ) ρ, ∀ μ, 0 < μ → μ ≤ 1 →
                μ = Ψ p ζ μ → m ≤ μ := by
              intro p hp ζ hζ μ h1 h2 h3
              by_contra hc
              have hc := not_le.mp hc
              have hs1 := hsmall p hp ζ hζ μ h1 (le_trans hc.le (min_le_left _ _))
              have hs2 : m ≤ φ x0 / 2 := min_le_right _ _
              linarith only [hs1, hs2, hc, h3]
            have hex : ∀ p ∈ Set.Icc lo hi, ∀ ζ ∈ Set.Ico (0:ℝ) ρ, ∃ μ ∈ Set.Ioc (0:ℝ) 1,
                μ = Ψ p ζ μ := by
              intro p hp ζ hζ
              have hm1 : m ≤ 1 := le_trans (min_le_left _ _) (min_le_left _ _)
              have hcont : ContinuousOn (fun μ => μ - Ψ p ζ μ) (Set.Icc (m / 2) 1) := by
                have hωc : ContinuousOn (fun μ => M.ω (M.d / μ)) (Set.Icc (m / 2) 1) := by
                  refine (hωsmooth.continuousOn).comp (continuousOn_const.div continuousOn_id ?_) ?_
                  · intro x hx; exact ne_of_gt (by linarith only [hx.1, hm0])
                  · intro x hx; exact Set.mem_Ioi.2 (div_pos hd (by linarith only [hx.1, hm0]))
                have hc1 : ∀ c, 0 ≤ c → ContinuousOn (fun μ => φ (c * M.ω (M.d / μ)))
                    (Set.Icc (m / 2) 1) := by
                  intro c hc
                  refine hφcont.comp (continuousOn_const.mul hωc) ?_
                  intro x hx
                  exact Set.mem_Ici.2 (mul_nonneg hc (hq0 x (by linarith only [hx.1, hm0]) hx.2).1)
                have : (fun μ => μ - Ψ p ζ μ) = fun μ => μ - (φ ((p + ζ) * M.ω (M.d / μ)) +
                    φ ((p - ζ) * M.ω (M.d / μ))) / 2 := funext fun μ => by rw [hΨ]
                rw [this]
                exact continuousOn_id.sub (((hc1 _ (by linarith only [hp.1, hζ.1, hlo])).add
                  (hc1 _ (by linarith only [hp.1, hζ.2, hρlo]))).div_const 2)
              have hIVT := intermediate_value_Icc (by linarith only [hm1, hm0]) hcont
              have hlo' : m / 2 - Ψ p ζ (m / 2) ≤ 0 := by
                have hmμ : m ≤ μ0 := min_le_left _ _
                have hs1 := hsmall p hp ζ hζ (m / 2) (by linarith only [hm0])
                  (by linarith only [hmμ, hm0])
                have hs2 : m ≤ φ x0 / 2 := min_le_right _ _
                linarith only [hs1, hs2, hm0]
              have hhi' : 0 ≤ 1 - Ψ p ζ 1 := by
                rw [hΨ]
                have hq := hq0 1 one_pos le_rfl
                have a1 := (hφ01 ((p + ζ) * M.ω (M.d / 1))
                  (mul_nonneg (by linarith only [hp.1, hζ.1, hlo]) hq.1)).2
                have a2 := (hφ01 ((p - ζ) * M.ω (M.d / 1))
                  (mul_nonneg (by linarith only [hp.1, hζ.2, hρlo]) hq.1)).2
                linarith only [a1, a2]
              obtain ⟨μ, hμ, hμ0'⟩ := hIVT ⟨hlo', hhi'⟩
              exact ⟨μ, ⟨by linarith only [hμ.1, hm0], hμ.2⟩, by simp only at hμ0'; linarith only [hμ0']⟩
            clear_value m ρ μ0 Y x0
            -- integral-level Taylor bounds
            have hφT1 : ∀ x h, 0 ≤ h → h ≤ x → |(φ (x + h) + φ (x - h)) / 2 - φ x| ≤ K / 2 * h ^ 2 := by
              intro x h hh hhx
              have i1 := hint (x + h) (by linarith only [hh, hhx])
              have i2 := hint (x - h) (by linarith only [hh, hhx])
              have i3 := hint x (by linarith only [hh, hhx])
              have eq : (φ (x + h) + φ (x - h)) / 2 - φ x =
                  ∫ b, ((M.f b (x + h) + M.f b (x - h)) / 2 - M.f b x) ∂M.β := by
                rw [hφ, hφ, hφ, ← integral_add i1 i2, ← integral_div,
                  ← integral_sub (by exact (i1.add i2).div_const 2 :
                    Integrable (fun b => (M.f b (x + h) + M.f b (x - h)) / 2) M.β) i3]
              rw [eq]
              calc _ ≤ ∫ b, |(M.f b (x + h) + M.f b (x - h)) / 2 - M.f b x| ∂M.β :=
                    abs_integral_le_integral_abs
                _ ≤ ∫ b, K / 2 * h ^ 2 ∂M.β :=
                    integral_mono (((i1.add i2).div_const 2).sub i3).abs (integrable_const _)
                      (fun b => hT1 b x h hh hhx)
                _ = K / 2 * h ^ 2 := by simp
            have hφT2 : ∀ x h, 0 ≤ h → h ≤ x →
                φ (x + h) - φ (x - h) ≤ 2 * h * (1 + K * (2 * h + 1) / 2) := by
              intro x h hh hhx
              have i1 := hint (x + h) (by linarith only [hh, hhx])
              have i2 := hint (x - h) (by linarith only [hh, hhx])
              rw [hφ, hφ, ← integral_sub i1 i2]
              calc _ ≤ ∫ b, 2 * h * (1 + K * (2 * h + 1) / 2) ∂M.β :=
                    integral_mono (i1.sub i2) (integrable_const _) (fun b => hT2 b x h hh hhx)
                _ = _ := by simp
            -- Lipschitz of r
            obtain ⟨C1, hC1⟩ := hrd 1 le_rfl
            have hrL : ∀ x y, 0 < x → 0 < y → |M.r y - M.r x| ≤ C1 * |y - x| := by
              intro x y hx hy
              have := Convex.norm_image_sub_le_of_norm_derivWithin_le
                (hrsmooth.differentiableOn (by simp)) (fun z hz => by
                  have := hC1 z hz; rw [iteratedDerivWithin_one] at this
                  rwa [Real.norm_eq_abs]) (convex_Ioi 0) (Set.mem_Ioi.2 hx) (Set.mem_Ioi.2 hy)
              simpa [Real.norm_eq_abs] using this
            have hC10 : 0 ≤ C1 := by
              have := hC1 1 one_pos; exact le_trans (abs_nonneg _) this
            -- Lipschitz of ω on [d, ∞)
            have hωL : ∀ x y, M.d ≤ x → x ≤ y → M.ω y - M.ω x ≤ (y - x) / M.d := by
              intro x y hx hxy
              have hy : 0 < y := lt_of_lt_of_le hd (hx.trans hxy)
              have hb0 : 0 ≤ x / y := div_nonneg (hd.le.trans hx) hy.le
              have hb1 : x / y ≤ 1 := (div_le_one hy).2 hxy
              have c := hωconc.2 (Set.mem_Ici.2 (le_refl (0:ℝ))) (Set.mem_Ici.2 hy.le)
                (sub_nonneg.2 hb1) hb0 (sub_add_cancel 1 (x / y))
              have e : (1 - x / y) • (0:ℝ) + (x / y) • y = x := by
                rw [smul_zero, zero_add, smul_eq_mul, div_mul_cancel₀ x hy.ne']
              rw [e] at c
              simp only [smul_eq_mul] at c
              have w0 := (hω01 0 le_rfl).1
              have wy := (hω01 y hy.le)
              have i1 : 0 ≤ (1 - x / y) * M.ω 0 := mul_nonneg (sub_nonneg.2 hb1) w0
              have h5 : M.ω y - M.ω x ≤ (1 - x / y) * M.ω y := by linarith only [c, i1]
              have h2 : (1 - x / y) * M.ω y ≤ (1 - x / y) := mul_le_of_le_one_right (sub_nonneg.2 hb1) wy.2
              have h3 : 1 - x / y = (y - x) / y := by rw [sub_div, div_self hy.ne']
              have h4 : (y - x) / y ≤ (y - x) / M.d :=
                div_le_div_of_nonneg_left (sub_nonneg.2 hxy) hd (hx.trans hxy)
              linarith only [h5, h2, h3, h4]
            have hωL' : ∀ x y, M.d ≤ x → M.d ≤ y → |M.ω y - M.ω x| ≤ |y - x| / M.d := by
              intro x y hx hy
              rcases le_total x y with h | h
              · have h1 := hωL x y hx h
                have h2 := hωmono (Set.mem_Ici.2 (hd.le.trans hx)) (Set.mem_Ici.2 (hd.le.trans hy)) h
                rw [abs_of_nonneg (sub_nonneg.2 h2), abs_of_nonneg (sub_nonneg.2 h)]; exact h1
              · have h1 := hωL y x hy h
                have h2 := hωmono (Set.mem_Ici.2 (hd.le.trans hy)) (Set.mem_Ici.2 (hd.le.trans hx)) h
                rw [abs_of_nonpos (sub_nonpos.2 h2), abs_of_nonpos (sub_nonpos.2 h)]
                have : -(y - x) / M.d = (x - y) / M.d := by ring
                linarith only [h1, this]
            have hinv : ∀ a c, m ≤ a → m ≤ c → |M.d / a - M.d / c| ≤ M.d / m ^ 2 * |a - c| := by
              intro a c ha hc
              have ha0 : 0 < a := lt_of_lt_of_le hm0 ha
              have hc0 : 0 < c := lt_of_lt_of_le hm0 hc
              have e : M.d / a - M.d / c = M.d * (c - a) / (a * c) := by
                rw [div_sub_div _ _ ha0.ne' hc0.ne']; ring
              rw [e, abs_div, abs_mul, abs_of_pos hd, abs_of_pos (mul_pos ha0 hc0), abs_sub_comm c a]
              have h7 : m ^ 2 ≤ a * c := by rw [sq]; exact mul_le_mul ha hc hm0.le ha0.le
              calc M.d * |a - c| / (a * c) ≤ M.d * |a - c| / m ^ 2 :=
                    div_le_div_of_nonneg_left (mul_nonneg hd.le (abs_nonneg _)) (pow_pos hm0 2) h7
                _ = M.d / m ^ 2 * |a - c| := by ring
            set L0 := 1 + K * (2 * lo + 1) / 2 with hL0
            set Lr := C1 * (M.d / m ^ 2) + |M.r M.d| + C1 * (M.d / m) with hLr
            set Lw := 1 / m ^ 2 + 1 with hLw
            have hLr0 : 0 ≤ Lr := add_nonneg (add_nonneg (mul_nonneg hC10 (div_nonneg hd.le (sq_nonneg m)))
              (abs_nonneg _)) (mul_nonneg hC10 (div_nonneg hd.le hm0.le))
            have hLw0 : 0 ≤ Lw := add_nonneg (div_nonneg zero_le_one (sq_nonneg m)) zero_le_one
            have hL00 : 0 ≤ L0 := add_nonneg zero_le_one
              (div_nonneg (mul_nonneg hK0 (by linarith only [hlo])) zero_le_two)
            refine ⟨(Lr + hi * Lw) * (K / 2) + L0 + 1, by
              have : 0 ≤ (Lr + hi * Lw) * (K / 2) :=
                mul_nonneg (add_nonneg hLr0 (mul_nonneg (hlo.le.trans hhi) hLw0)) (div_nonneg hK0 zero_le_two)
              linarith only [this, hL00], ρ, hρ0, hρlo, fun p hp ζ hζ => ?_⟩
            have hp0 : 0 < p := lt_of_lt_of_le hlo hp.1
            have hζ0 : 0 ≤ ζ := hζ.1
            have hζρ : ζ < ρ := hζ.2
            have hpζ : 0 < p - ζ := sub_pos.2 (lt_of_lt_of_le (lt_trans hζρ hρlo) hp.1)
            have final : ∀ a c qa qc : ℝ, a ∈ Set.Ioc (0:ℝ) 1 → c ∈ Set.Ioc (0:ℝ) 1 → m ≤ a → m ≤ c →
                (0 ≤ qa ∧ qa ≤ 1) → (0 ≤ qc ∧ qc ≤ 1) → a = φ (p * qa) →
                c = (φ ((p + ζ) * qc) + φ ((p - ζ) * qc)) / 2 →
                (a ≤ c → φ (p * qc) ≤ φ (p * qa)) → (c ≤ a → φ (p * qa) ≤ φ (p * qc)) →
                qa = M.ω (M.d / a) → qc = M.ω (M.d / c) →
                (M.r (M.d / a) - p * qa) * a - (M.r (M.d / c) * c - qc * (((p + ζ) * φ ((p + ζ) * qc) +
                  (p - ζ) * φ ((p - ζ) * qc)) / 2)) ≤ ((Lr + hi * Lw) * (K / 2) + L0 + 1) * ζ ^ 2 := by
              intro a c qa qc ha hc ham hcm hqa0 hqc0 hafix hcfixΨ han1 han2 hqa hqc
              have hzq0 : 0 ≤ ζ * qc := mul_nonneg hζ0 hqc0.1
              have hzq1 : ζ * qc ≤ p * qc :=
                mul_le_mul_of_nonneg_right (by linarith only [hp.1, hζρ, hρlo]) hqc0.1
              have g1 : ζ * qc ≤ ζ := mul_le_of_le_one_right hζ0 hqc0.2
              have e1 : (p + ζ) * qc = p * qc + ζ * qc := by ring
              have e2 : (p - ζ) * qc = p * qc - ζ * qc := by ring
              have he : |(φ ((p + ζ) * qc) + φ ((p - ζ) * qc)) / 2 - φ (p * qc)| ≤ K / 2 * ζ ^ 2 := by
                have := hφT1 (p * qc) (ζ * qc) hzq0 hzq1
                rw [e1, e2]
                have hsq : (ζ * qc) ^ 2 ≤ ζ ^ 2 := by
                  rw [mul_pow]; exact mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ hqc0.1 hqc0.2)
                exact this.trans (mul_le_mul_of_nonneg_left hsq (by linarith only [hK0]))
              have hac : |a - c| ≤ K / 2 * ζ ^ 2 := by
                rw [abs_le] at he ⊢
                rcases le_total a c with h | h
                · have := han1 h
                  constructor <;> linarith only [he.1, he.2, this, hafix, hcfixΨ, h]
                · have := han2 h
                  constructor <;> linarith only [he.1, he.2, this, hafix, hcfixΨ, h]
              have hD0 : 0 ≤ φ ((p + ζ) * qc) - φ ((p - ζ) * qc) := by
                have := hφmono ((p - ζ) * qc) ((p + ζ) * qc) (mul_nonneg hpζ.le hqc0.1)
                  (mul_le_mul_of_nonneg_right (by linarith only [hζ0]) hqc0.1)
                linarith only [this]
              have hD : φ ((p + ζ) * qc) - φ ((p - ζ) * qc) ≤ 2 * ζ * L0 := by
                have := hφT2 (p * qc) (ζ * qc) hzq0 hzq1
                rw [e1, e2]
                have g2 : 1 + K * (2 * (ζ * qc) + 1) / 2 ≤ L0 := by
                  have : K * (ζ * qc) ≤ K * lo :=
                    mul_le_mul_of_nonneg_left (by linarith only [g1, hζρ, hρlo]) hK0
                  rw [hL0]; linarith only [this]
                have g3 : 2 * (ζ * qc) * (1 + K * (2 * (ζ * qc) + 1) / 2) ≤ 2 * ζ * L0 :=
                  mul_le_mul (by linarith only [g1]) g2
                    (by have := mul_nonneg hK0 hzq0; linarith only [this, hK0]) (by linarith only [hζ0])
                linarith only [g3, this]
              have hT3 : qc * ζ * (φ ((p + ζ) * qc) - φ ((p - ζ) * qc)) / 2 ≤ ζ ^ 2 * L0 := by
                have i1 : qc * (ζ * (φ ((p + ζ) * qc) - φ ((p - ζ) * qc))) ≤
                    1 * (ζ * (φ ((p + ζ) * qc) - φ ((p - ζ) * qc))) :=
                  mul_le_mul_of_nonneg_right hqc0.2 (mul_nonneg hζ0 hD0)
                have i2 : ζ * (φ ((p + ζ) * qc) - φ ((p - ζ) * qc)) ≤ ζ * (2 * ζ * L0) :=
                  mul_le_mul_of_nonneg_left hD hζ0
                linarith only [i1, i2]
              have hdc : M.d ≤ M.d / c := hdμ c hc.1 hc.2
              have hda : M.d ≤ M.d / a := hdμ a ha.1 ha.2
              have hc0 : 0 < M.d / c := lt_of_lt_of_le hd hdc
              have ha0 : 0 < M.d / a := lt_of_lt_of_le hd hda
              have hI := hinv a c ham hcm
              have hX : |M.r (M.d / a) - M.r (M.d / c)| ≤ C1 * (M.d / m ^ 2) * |a - c| := by
                have := hrL (M.d / c) (M.d / a) hc0 ha0
                rw [mul_assoc]; exact this.trans (mul_le_mul_of_nonneg_left hI hC10)
              have hY : |M.r (M.d / c)| ≤ |M.r M.d| + C1 * (M.d / m) := by
                have h1 := hrL M.d (M.d / c) hd hc0
                have h2 : |M.d / c - M.d| ≤ M.d / m := by
                  rw [abs_of_nonneg (by linarith only [hdc])]
                  have : M.d / c ≤ M.d / m := div_le_div_of_nonneg_left hd.le hm0 hcm
                  linarith only [this, hd]
                have h3 := abs_sub_abs_le_abs_sub (M.r (M.d / c)) (M.r M.d)
                have h4 := mul_le_mul_of_nonneg_left h2 hC10
                linarith only [h1, h3, h4]
              have hZ : |qa - qc| ≤ 1 / m ^ 2 * |a - c| := by
                rw [hqa, hqc]
                have h1 := hωL' (M.d / c) (M.d / a) hdc hda
                have h2 : |M.d / a - M.d / c| / M.d ≤ (M.d / m ^ 2 * |a - c|) / M.d :=
                  div_le_div_of_nonneg_right hI hd.le
                have h3 : (M.d / m ^ 2 * |a - c|) / M.d = 1 / m ^ 2 * |a - c| := by
                  field_simp
                linarith only [h1, h2, h3]
              have hX0 : 0 ≤ C1 * (M.d / m ^ 2) := mul_nonneg hC10 (div_nonneg hd.le (sq_nonneg m))
              have hY0 : 0 ≤ |M.r M.d| + C1 * (M.d / m) :=
                add_nonneg (abs_nonneg _) (mul_nonneg hC10 (div_nonneg hd.le hm0.le))
              have hZ0 : 0 ≤ 1 / m ^ 2 := div_nonneg zero_le_one (sq_nonneg m)
              have := alg a c qa qc (M.r (M.d / a)) (M.r (M.d / c)) p ζ (φ ((p + ζ) * qc))
                (φ ((p - ζ) * qc)) (C1 * (M.d / m ^ 2)) (|M.r M.d| + C1 * (M.d / m)) (1 / m ^ 2)
                (K / 2 * ζ ^ 2) L0 hi ha.1.le ha.2 hqc0.1 hqc0.2 hp0.le hp.2 hX0 hY0 hZ0
                hX hY hZ hac hcfixΨ hT3
              have hsum : C1 * (M.d / m ^ 2) + (|M.r M.d| + C1 * (M.d / m)) + hi * (1 / m ^ 2 + 1) =
                  Lr + hi * Lw := by
                rw [hLr, hLw]; ring
              rw [hsum] at this
              have hz2 := sq_nonneg ζ
              linarith only [this, hz2]
            have hanti : ∀ μ ν, 0 < μ → μ ≤ ν → φ (p * M.ω (M.d / ν)) ≤ φ (p * M.ω (M.d / μ)) := by
              intro μ ν h1 h2
              have hν : 0 < ν := lt_of_lt_of_le h1 h2
              have hdd : M.d / ν ≤ M.d / μ := div_le_div_of_nonneg_left hd.le h1 h2
              have w1 := hω01 (M.d / ν) (by positivity)
              have w2 := hωmono (Set.mem_Ici.2 (by positivity : (0:ℝ) ≤ M.d / ν))
                (Set.mem_Ici.2 (by positivity : (0:ℝ) ≤ M.d / μ)) hdd
              exact hφmono _ _ (mul_nonneg hp0.le w1.1) (mul_le_mul_of_nonneg_left w2 hp0.le)
            have hexL : ∃ μ ∈ Set.Ioc (0:ℝ) 1, μ = ∫ b, M.f b (p * M.ω (M.d / μ)) ∂M.β := by
              obtain ⟨μ, hμ, he⟩ := hex p hp 0 ⟨le_rfl, hρ0⟩
              refine ⟨μ, hμ, ?_⟩
              rw [hΨ, add_zero, sub_zero, add_self_div_two] at he; rw [← hφ]; exact he
            obtain ⟨ha, hafix⟩ : M.muLim p ∈ Set.Ioc (0:ℝ) 1 ∧
                M.muLim p = ∫ b, M.f b (p * M.ω (M.d / M.muLim p)) ∂M.β := by
              have e : M.muLim p = hexL.choose := by unfold Market.muLim; rw [dif_pos hexL]
              rw [e]; exact hexL.choose_spec
            rw [← hφ] at hafix
            have hpsi : ∀ μ, 0 < μ → μ ≤ 1 → psiPert M p ζ μ = Ψ p ζ μ := by
              intro μ h1 h2
              have hq := hq0 μ h1 h2
              unfold psiPert
              simp_rw [hPL]
              rw [integral_div, integral_add (hint ((p + ζ) * M.ω (M.d / μ))
                  (mul_nonneg (by linarith only [hp0, hζ0]) hq.1))
                (hint ((p - ζ) * M.ω (M.d / μ)) (mul_nonneg hpζ.le hq.1)), ← hφ, ← hφ, hΨ]
            have hexP : ∃ μ ∈ Set.Ioc (0:ℝ) 1, μ = psiPert M p ζ μ := by
              obtain ⟨μ, hμ, he⟩ := hex p hp ζ hζ
              exact ⟨μ, hμ, by rw [hpsi μ hμ.1 hμ.2]; exact he⟩
            obtain ⟨hc, hcfix⟩ : muPert M p ζ ∈ Set.Ioc (0:ℝ) 1 ∧
                muPert M p ζ = psiPert M p ζ (muPert M p ζ) := by
              have e : muPert M p ζ = hexP.choose := by rw [muPert, dif_pos hexP]
              rw [e]; exact hexP.choose_spec
            have hcfixΨ : muPert M p ζ = Ψ p ζ (muPert M p ζ) := hcfix.trans (hpsi _ hc.1 hc.2)
            have hcm : m ≤ muPert M p ζ := hlow p hp ζ hζ _ hc.1 hc.2 hcfixΨ
            rw [hΨ] at hcfixΨ
            clear hcfix
            have hqc0 := hq0 _ hc.1 hc.2
            have hpay : ∫ b, ∫ P, P * M.f b (P * qPert M p ζ) ∂(perturbLaw p ζ) ∂M.β =
                ((p + ζ) * φ ((p + ζ) * qPert M p ζ) + (p - ζ) * φ ((p - ζ) * qPert M p ζ)) / 2 := by
              simp_rw [hPL]
              rw [integral_div, integral_add ((hint ((p + ζ) * qPert M p ζ)
                  (mul_nonneg (by linarith only [hp0, hζ0]) hqc0.1)).const_mul (p + ζ))
                ((hint ((p - ζ) * qPert M p ζ) (mul_nonneg hpζ.le hqc0.1)).const_mul (p - ζ)),
                integral_const_mul, integral_const_mul, ← hφ, ← hφ]
            have hU : uPert M p ζ = M.r (M.d / muPert M p ζ) * muPert M p ζ -
                qPert M p ζ * (((p + ζ) * φ ((p + ζ) * qPert M p ζ) +
                  (p - ζ) * φ ((p - ζ) * qPert M p ζ)) / 2) := by
              unfold uPert; rw [hpay]
            have hu : M.u p = (M.r (M.d / M.muLim p) - p * M.ω (M.d / M.muLim p)) * M.muLim p := rfl
            have hqP : qPert M p ζ = M.ω (M.d / muPert M p ζ) := rfl
            rw [hu, hU, hqP]
            have hqa0 := hq0 _ ha.1 ha.2
            have ham : m ≤ M.muLim p := hlow p hp 0 ⟨le_rfl, hρ0⟩ _ ha.1 ha.2
              (by rw [hΨ, add_zero, sub_zero, add_self_div_two]; exact hafix)
            exact final _ _ _ _ ha hc ham hcm hqa0 hqc0 hafix hcfixΨ (hanti _ _ ha.1) (hanti _ _ hc.1) rfl rfl
          have hkey := fun a => key (E.market a) (hE a) (hpos a)
          choose C hC ρ hρ hρlo hb using hkey
          refine ⟨∑ a, C a, Finset.sum_pos (fun a _ => hC a) Finset.univ_nonempty,
            Finset.univ.inf' Finset.univ_nonempty ρ, ?_, ?_, ?_⟩
          · exact (Finset.lt_inf'_iff _).2 (fun a _ => hρ a)
          · obtain ⟨a⟩ := ‹Nonempty A›
            exact lt_of_le_of_lt (Finset.inf'_le _ (Finset.mem_univ a)) (hρlo a)
          · intro T hT states payments hpay ζ hζ
            have hTpos : (0:ℝ) < T := by exact_mod_cast hT
            rw [div_le_iff₀ hTpos]
            have hs : ∀ t, (E.market (states t)).u (payments t) -
                uPert (E.market (states t)) (payments t) ζ ≤ (∑ a, C a) * ζ ^ 2 := by
              intro t
              have hζ' : ζ ∈ Set.Ico (0:ℝ) (ρ (states t)) :=
                ⟨hζ.1, lt_of_lt_of_le hζ.2 (Finset.inf'_le _ (Finset.mem_univ _))⟩
              have h1 := hb (states t) (payments t) (hpay t) ζ hζ'
              have h2 : C (states t) ≤ ∑ a, C a :=
                Finset.single_le_sum (fun a _ => (hC a).le) (Finset.mem_univ _)
              have h3 := mul_le_mul_of_nonneg_right h2 (sq_nonneg ζ)
              linarith only [h1, h3]
            calc _ ≤ ∑ t : Fin T, (∑ a, C a) * ζ ^ 2 := Finset.sum_le_sum (fun t _ => hs t)
              _ = (∑ a, C a) * ζ ^ 2 * T := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
