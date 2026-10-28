-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_delta_nearMaximizer_norm_sub_gradient_lt_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:32:53.147235+00:00
-- url     : https://prove2.me/submissions/f7394aa6-4f56-4237-a584-1b69f10d7e98

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_LegendreVariation_Derivative

section
noncomputable section
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- One finite value excludes `-∞` for the entire Legendre transform. -/
theorem FunctionalInequalities.Analysis.legendre_ne_bot (φ : E → EReal) (hφ : ProperPotential φ) (y : E) :
    legendre φ y ≠ ⊥ := by
  obtain ⟨x, hx⟩ := hφ.2
  have hb := hφ.1 x
  lift φ x to ℝ using ⟨hx, hb⟩ with r hr
  have hle : ((inner ℝ x y - r : ℝ) : EReal) ≤ legendre φ y := by
    change ((inner ℝ x y - r : ℝ) : EReal) ≤
      ⨆ z : E, (inner ℝ z y : EReal) - φ z
    simpa only [← hr, EReal.coe_sub] using
      (le_iSup (fun z : E => (inner ℝ z y : EReal) - φ z) x)
  exact ne_of_gt ((EReal.bot_lt_coe _).trans_le hle)
/-- Fenchel inequality for a proper extended potential; no convexity is assumed. -/
theorem FunctionalInequalities.Analysis.fenchel_le (φ : E → EReal) (hφ : ProperPotential φ) (x y : E) :
    (inner ℝ x y : EReal) ≤ φ x + legendre φ y := by
  have h := le_iSup (fun z : E => (inner ℝ z y : EReal) - φ z) x
  have hi := (EReal.sub_le_iff_le_add (.inl (hφ.1 x))
    (.inr (legendre_ne_bot φ hφ y))).mp h
  simpa only [add_comm] using hi
end
end
end

noncomputable section
section NearMaximizer
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set
/-- Actual affine terms that approach the finite conjugate value concentrate
near the dual gradient. The near-maximality inequality is the quantified
antecedent, rather than a supplied stability or selected-maximizer premise. -/
theorem solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (φ : E → EReal) (hφ : FunctionalInequalities.Analysis.ProperPotential φ) (y : E)
    (hy : y ∈ interior {q : E | FunctionalInequalities.Analysis.legendre φ q ≠ ⊤})
    (hd : DifferentiableAt ℝ (fun q : E => (FunctionalInequalities.Analysis.legendre φ q).toReal) y) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ z : E,
      (((FunctionalInequalities.Analysis.legendre φ y).toReal - δ : ℝ) : EReal) ≤
          (inner ℝ z y : EReal) - φ z →
        ‖z - gradient (fun q : E => (FunctionalInequalities.Analysis.legendre φ q).toReal) y‖ < ε := by
    let F : E → ℝ := fun q => (FunctionalInequalities.Analysis.legendre φ q).toReal
    have hdF : DifferentiableAt ℝ F y := by
      simpa [F] using hd
    have hφ_bot : ∀ x : E, φ x ≠ ⊥ := by
      have hh := hφ
      simp [FunctionalInequalities.Analysis.ProperPotential] at hh
      aesop
    have hφ_fin : ∃ x : E, φ x ≠ ⊤ := by
      have hh := hφ
      simp [FunctionalInequalities.Analysis.ProperPotential] at hh
      aesop
    have hleg_bot : ∀ q : E, FunctionalInequalities.Analysis.legendre φ q ≠ ⊥ := by
      rcases hφ_fin with ⟨x, hx⟩
      intro q hq
      have hf := FunctionalInequalities.Analysis.fenchel_le φ hφ x q
      rw [hq] at hf
      have hf' : (inner ℝ x q : EReal) ≤ ⊥ := by
        simpa only [EReal.add_bot] using hf
      exact (not_le_of_gt (EReal.bot_lt_coe _)) hf'
    have hy_top : FunctionalInequalities.Analysis.legendre φ y ≠ ⊤ :=
      interior_subset hy
    have hLy : ((F y : ℝ) : EReal) = FunctionalInequalities.Analysis.legendre φ y := by
      dsimp [F]
      exact EReal.coe_toReal hy_top (hleg_bot y)
    have htop_ev : ∀ᶠ q : E in nhds y, FunctionalInequalities.Analysis.legendre φ q ≠ ⊤ := by
      exact mem_interior_iff_mem_nhds.mp hy
    have hsmall :
        (fun q => F q - F y - fderiv ℝ F y (q - y)) =o[nhds y]
          (fun q => q - y) :=
      hdF.hasFDerivAt.isLittleO
    intro ε hε
    have hrem_ev :
        ∀ᶠ q : E in nhds y,
          ‖F q - F y - fderiv ℝ F y (q - y)‖
            ≤ (ε / 4) * ‖q - y‖ := by
      exact
        (Asymptotics.isLittleO_iff.mp hsmall) (c := ε / 4) (by linarith)
    rcases (Metric.eventually_nhds_iff.mp htop_ev) with ⟨ρ, hρ, hρtop⟩
    rcases (Metric.eventually_nhds_iff.mp hrem_ev) with ⟨η, hη, hηrem⟩
    let r : ℝ := min ρ η / 2
    have hr : 0 < r := by
      dsimp [r]
      positivity
    have hrρ : r < ρ := by
      dsimp [r]
      have hmin : min ρ η ≤ ρ := min_le_left _ _
      linarith
    have hrη : r < η := by
      dsimp [r]
      have hmin : min ρ η ≤ η := min_le_right _ _
      linarith
    let δ : ℝ := r * (ε / 4)
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    refine ⟨δ, hδ, ?_⟩
    intro z hp
    change ‖z - gradient F y‖ < ε
    by_cases hzg : z = gradient F y
    · subst z
      simp
      linarith
    let w : E := z - gradient F y
    have hw : w ≠ 0 := by
      dsimp [w]
      exact sub_ne_zero.mpr hzg
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
    let u : E := ‖w‖⁻¹ • w
    have hu : ‖u‖ = 1 := by
      dsimp [u]
      rw [norm_smul]
      simp [hwpos.ne']
    let h : E := r • u
    have hh : ‖h‖ = r := by
      dsimp [h]
      simp [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hu]
    let q : E := y + h
    have hqdist : dist q y = r := by
      rw [dist_eq_norm]
      dsimp [q]
      rw [add_sub_cancel_left, hh]
    have hqρ : dist q y < ρ := by
      rw [hqdist]
      exact hrρ
    have hqη : dist q y < η := by
      rw [hqdist]
      exact hrη
    have hqtop : FunctionalInequalities.Analysis.legendre φ q ≠ ⊤ := hρtop hqρ
    have hLq : ((F q : ℝ) : EReal) = FunctionalInequalities.Analysis.legendre φ q := by
      dsimp [F]
      exact EReal.coe_toReal hqtop (hleg_bot q)
    have hzbot : φ z ≠ ⊥ := hφ_bot z
    have hztop : φ z ≠ ⊤ := by
      intro hzt
      have hp' := hp
      rw [hzt, EReal.sub_top] at hp'
      exact (not_le_of_gt (EReal.bot_lt_coe _)) hp'
    have hfen := FunctionalInequalities.Analysis.fenchel_le φ hφ z q
    have hsum :
        (inner ℝ z q : EReal) + ((F y - δ : ℝ) : EReal)
          ≤ FunctionalInequalities.Analysis.legendre φ q + (inner ℝ z y : EReal) := by
      calc
        (inner ℝ z q : EReal) + ((F y - δ : ℝ) : EReal)
            ≤ (φ z + FunctionalInequalities.Analysis.legendre φ q) +
                ((inner ℝ z y : EReal) - φ z) :=
          add_le_add hfen hp
        _ = FunctionalInequalities.Analysis.legendre φ q + (inner ℝ z y : EReal) := by
          have hφz : ((φ z).toReal : EReal) = φ z :=
            EReal.coe_toReal hztop hzbot
          rw [← hφz, ← hLq]
          simp only [← EReal.coe_add, ← EReal.coe_sub]
          congr 1
          ring
    have hreal :
        inner ℝ z q + (F y - δ) ≤ F q + inner ℝ z y := by
      apply EReal.coe_le_coe_iff.mp
      calc
        ((inner ℝ z q + (F y - δ) : ℝ) : EReal)
            = (inner ℝ z q : EReal) + ((F y - δ : ℝ) : EReal) := by
              norm_num
        _ ≤ FunctionalInequalities.Analysis.legendre φ q + (inner ℝ z y : EReal) := hsum
        _ = ((F q + inner ℝ z y : ℝ) : EReal) := by
          rw [← hLq]
          norm_num
    have hrel :
        inner ℝ z (q - y) ≤ F q - F y + δ := by
      calc
        inner ℝ z (q - y) = inner ℝ z q - inner ℝ z y := by
          rw [inner_sub_right]
        _ ≤ F q - F y + δ := by
          linarith
    have hgrad :
        (InnerProductSpace.toDual ℝ E) (gradient F y) = fderiv ℝ F y :=
      toDual_gradient
    have hderiv (v : E) :
        fderiv ℝ F y v = inner ℝ (gradient F y) v := by
      rw [← hgrad]
      rfl
    have hqnorm : ‖q - y‖ = r := by
      dsimp [q]
      rw [add_sub_cancel_left, hh]
    have hrem :
        F q - F y - inner ℝ (gradient F y) h ≤ (ε / 4) * r := by
      calc
        F q - F y - inner ℝ (gradient F y) h
            = F q - F y - fderiv ℝ F y h := by
              rw [hderiv]
        _ ≤ ‖F q - F y - fderiv ℝ F y (q - y)‖ := by
              rw [show q - y = h by
                dsimp [q]
                exact add_sub_cancel_left y h]
              simpa only [Real.norm_eq_abs] using (le_abs_self _)
        _ ≤ (ε / 4) * ‖q - y‖ := hηrem hqη
        _ = (ε / 4) * r := by rw [hqnorm]
    have hbound :
        inner ℝ (z - gradient F y) h ≤ (ε / 4) * r + δ := by
      calc
        inner ℝ (z - gradient F y) h
            = inner ℝ z h - inner ℝ (gradient F y) h := by
              rw [inner_sub_left]
        _ ≤ (F q - F y + δ) - inner ℝ (gradient F y) h := by
              have := hrel
              dsimp [q] at this
              rw [add_sub_cancel_left] at this
              linarith
        _ = (F q - F y - inner ℝ (gradient F y) h) + δ := by
              ring
        _ ≤ (ε / 4) * r + δ := by
              linarith
    have hleft :
        inner ℝ (z - gradient F y) h = r * ‖z - gradient F y‖ := by
      dsimp [w, h, u]
      rw [real_inner_smul_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq]
      field_simp [ne_of_gt hwpos]
    have hmul :
        r * ‖z - gradient F y‖ ≤ r * (ε / 2) := by
      calc
        r * ‖z - gradient F y‖ =
            inner ℝ (z - gradient F y) h := hleft.symm
        _ ≤ (ε / 4) * r + δ := hbound
        _ = r * (ε / 2) := by
          dsimp [δ]
          ring
    have hnorm : ‖z - gradient F y‖ ≤ ε / 2 := by
      nlinarith [hmul]
    linarith
