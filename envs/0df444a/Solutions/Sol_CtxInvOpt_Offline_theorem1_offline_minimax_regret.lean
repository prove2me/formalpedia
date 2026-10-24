-- Prove2me | solution 1 for CtxInvOpt.Offline.theorem1_offline_minimax_regret
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T03:28:56.375129+00:00
-- url     : https://prove2.me/submissions/1ff24464-8e5b-48f1-b34a-60507aa2f95f

import Mathlib
import Definitions.Def_CtxInvOpt_Offline_Geometry
import Definitions.Def_CtxInvOpt_Offline_Data

set_option autoImplicit false

namespace CtxInvOpt.Offline.Pf20ea

open CtxInvOpt.Offline Real

lemma mem_unitSphere_iff {d : ℕ} (c : EuclideanSpace ℝ (Fin d)) :
    c ∈ unitSphere d ↔ ‖c‖ = 1 := by
  simp [unitSphere]

lemma vecAngle_unit {d : ℕ} {c chat : EuclideanSpace ℝ (Fin d)} (hc : ‖c‖ = 1)
    (hh : ‖chat‖ = 1) : vecAngle c chat = Real.arccos (inner ℝ c chat) := by
  unfold vecAngle
  have h1 : c ≠ 0 := by rintro rfl; simp at hc
  have h2 : chat ≠ 0 := by rintro rfl; simp at hh
  rw [if_neg (by tauto)]
  simp [hc, hh]

lemma vecAngle_nonneg {d : ℕ} (c chat : EuclideanSpace ℝ (Fin d)) : 0 ≤ vecAngle c chat := by
  unfold vecAngle
  split_ifs
  · exact le_rfl
  · exact Real.arccos_nonneg _

lemma vecAngle_le_pi {d : ℕ} (c chat : EuclideanSpace ℝ (Fin d)) : vecAngle c chat ≤ π := by
  unfold vecAngle
  split_ifs
  · exact Real.pi_pos.le
  · exact Real.arccos_le_pi _

lemma bdd {d : ℕ} (C : Set (EuclideanSpace ℝ (Fin d))) (chat : EuclideanSpace ℝ (Fin d)) :
    BddAbove (Set.range fun c : C => vecAngle (c : EuclideanSpace ℝ (Fin d)) chat) :=
  ⟨π, by rintro _ ⟨c, rfl⟩; exact vecAngle_le_pi _ _⟩

/-- Part (a): the circumcenter policy's regret bound. -/
lemma partA {n d : ℕ} (C : Set (EuclideanSpace ℝ (Fin d))) (chat : EuclideanSpace ℝ (Fin d))
    (hcc : IsCircumcenter C chat) (cstar : EuclideanSpace ℝ (Fin d)) (hcs : cstar ∈ C)
    (hCs : C ⊆ unitSphere d) (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d))
    (hX : IsActionSet X) (hf : IsContext f) (xpi : EuclideanSpace ℝ (Fin n))
    (hxpi : xpi ∈ argminSet chat X f) (xstar : EuclideanSpace ℝ (Fin n))
    (hxs : xstar ∈ argminSet cstar X f) :
    inner ℝ (f xpi - f xstar) cstar ≤ regretCap (uncAngle C) := by
  have hcs1 : ‖cstar‖ = 1 := (mem_unitSphere_iff _).1 (hCs hcs)
  have hch1 : ‖chat‖ = 1 := (mem_unitSphere_iff _).1 hcc.1
  have hv : ‖f xpi - f xstar‖ ≤ 1 := by
    have h1 : dist (f xpi) (f xstar) ≤ ((1 : NNReal) : ℝ) * dist xpi xstar := hf.dist_le_mul _ _
    have h2 : dist xpi xstar ≤ Metric.diam X :=
      Metric.dist_le_diam_of_mem hX.2.1.isBounded hxpi.1 hxs.1
    rw [← dist_eq_norm]
    have h3 := hX.2.2
    simp only [NNReal.coe_one, one_mul] at h1
    linarith
  have hvc : inner ℝ (f xpi - f xstar) chat ≤ 0 := by
    have := hxpi.2 xstar hxs.1
    rw [inner_sub_left]
    linarith
  have hθ : vecAngle cstar chat ≤ uncAngle C := by
    rw [← hcc.2]
    exact le_ciSup (bdd C chat) ⟨cstar, hcs⟩
  rw [vecAngle_unit hcs1 hch1] at hθ
  unfold regretCap
  split_ifs with hα
  · set t := inner ℝ cstar chat with ht_def
    set v := f xpi - f xstar with hv_def
    have ht : 0 < t := Real.arccos_lt_pi_div_two.mp (lt_of_le_of_lt hθ hα)
    have key : inner ℝ v cstar ≤ ‖cstar - t • chat‖ := by
      have e1 : inner ℝ v cstar = t * inner ℝ v chat + inner ℝ v (cstar - t • chat) := by
        rw [inner_sub_right, inner_smul_right]; ring
      have e2 : inner ℝ v (cstar - t • chat) ≤ ‖v‖ * ‖cstar - t • chat‖ := real_inner_le_norm _ _
      have e3 : ‖v‖ * ‖cstar - t • chat‖ ≤ ‖cstar - t • chat‖ :=
        mul_le_of_le_one_left (norm_nonneg _) hv
      have e4 : t * inner ℝ v chat ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.le hvc
      linarith
    have hw : ‖cstar - t • chat‖ = Real.sin (arccos t) := by
      rw [Real.sin_arccos]
      have hsq : ‖cstar - t • chat‖ ^ 2 = 1 - t ^ 2 := by
        rw [@norm_sub_sq_real, norm_smul, inner_smul_right, hcs1, hch1, Real.norm_eq_abs,
          ← ht_def]
        have : |t| ^ 2 = t ^ 2 := sq_abs t
        nlinarith
      rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
    have hsin : Real.sin (arccos t) ≤ Real.sin (uncAngle C) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [Real.arccos_nonneg t, Real.pi_pos]) hα.le hθ
    linarith
  · calc inner ℝ (f xpi - f xstar) cstar ≤ ‖f xpi - f xstar‖ * ‖cstar‖ := real_inner_le_norm _ _
      _ ≤ 1 := by rw [hcs1]; linarith

/-- For a unit `chat` there is a unit `c` with `C ≤ ⟪c, e⟫` and `⟪c, chat⟫ ≤ C`, where
`C = cos a`, `S = sin a ≥ 0`. -/
lemma far {d : ℕ} (e w chat : EuclideanSpace ℝ (Fin d)) (he : inner ℝ e e = (1 : ℝ))
    (hw : inner ℝ w w = (1 : ℝ)) (hew : inner ℝ e w = (0 : ℝ)) (hc : ‖chat‖ = 1)
    (C S : ℝ) (hCS : C ^ 2 + S ^ 2 = 1) (hS : 0 ≤ S) :
    ∃ c : EuclideanSpace ℝ (Fin d), ‖c‖ = 1 ∧ C ≤ inner ℝ c e ∧ inner ℝ c chat ≤ C := by
  set s := inner ℝ chat e with hs
  set p := chat - s • e with hp
  have hpe : inner ℝ p e = 0 := by
    rw [hp, inner_sub_left, inner_smul_left, he]; simp [hs]
  have hchat_eq : chat = p + s • e := by rw [hp]; abel
  set r := ‖p‖ with hr
  -- an orthonormal partner `w'` with `chat = s e + r w'`
  obtain ⟨w', hw'1, hw'e, hw'c⟩ : ∃ w' : EuclideanSpace ℝ (Fin d),
      inner ℝ w' w' = (1 : ℝ) ∧ inner ℝ w' e = (0 : ℝ) ∧ inner ℝ w' chat = r := by
    by_cases hp0 : p = 0
    · refine ⟨w, hw, by rw [real_inner_comm]; exact hew, ?_⟩
      rw [hchat_eq, hp0, hr, hp0]
      simp [inner_smul_right, real_inner_comm, hew]
    · have hrpos : 0 < r := norm_pos_iff.mpr hp0
      refine ⟨r⁻¹ • p, ?_, ?_, ?_⟩
      · rw [inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq, ← hr]
        simp; field_simp
      · rw [inner_smul_left, hpe]; simp
      · rw [inner_smul_left, hchat_eq, inner_add_right, inner_smul_right, hpe,
          real_inner_self_eq_norm_sq, ← hr]
        simp; field_simp
  have hsr : s ^ 2 + r ^ 2 = 1 := by
    have h1 : inner ℝ chat chat = (1 : ℝ) := by
      rw [real_inner_self_eq_norm_sq, hc]; norm_num
    rw [hchat_eq, inner_add_left, inner_add_right, inner_add_right, inner_smul_left,
      inner_smul_right, inner_smul_left, inner_smul_right, hpe, real_inner_comm p e, hpe,
      real_inner_self_eq_norm_sq, he, ← hr] at h1
    simp at h1
    nlinarith
  have hs1 : s ≤ 1 := by nlinarith [sq_nonneg (s - 1), sq_nonneg r]
  have hr0 : 0 ≤ r := norm_nonneg _
  -- generic computation for `c = a • e + b • w'`
  have gen : ∀ a b : ℝ, a ^ 2 + b ^ 2 = 1 →
      ‖a • e + b • w'‖ = 1 ∧ inner ℝ (a • e + b • w') e = a ∧
        inner ℝ (a • e + b • w') chat = a * s + b * r := by
    intro a b hab
    have hce : inner ℝ (a • e + b • w') e = a := by
      rw [inner_add_left, inner_smul_left, inner_smul_left, he, hw'e]; simp
    have hcc : inner ℝ (a • e + b • w') chat = a * s + b * r := by
      rw [inner_add_left, inner_smul_left, inner_smul_left, hw'c, real_inner_comm chat e]
      simp [hs]
    have hsq : inner ℝ (a • e + b • w') (a • e + b • w') = (1 : ℝ) := by
      rw [inner_add_left, inner_add_right, inner_add_right, inner_smul_left, inner_smul_right,
        inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right, inner_smul_left,
        inner_smul_right, he, hw'1, real_inner_comm w' e, hw'e]
      simp
      nlinarith
    refine ⟨?_, hce, hcc⟩
    rw [real_inner_self_eq_norm_sq] at hsq
    have h0 : 0 ≤ ‖a • e + b • w'‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖a • e + b • w'‖ - 1)]
  rcases le_or_gt 0 C with hC | hC
  · obtain ⟨h1, h2, h3⟩ := gen C (-S) (by nlinarith)
    refine ⟨C • e + (-S) • w', h1, h2.ge, ?_⟩
    rw [h3]
    nlinarith [mul_nonneg hS hr0, mul_le_mul_of_nonneg_left hs1 hC]
  · obtain ⟨h1, h2, h3⟩ := gen (C * s + S * r) (C * r - S * s)
      (by rw [show (C * s + S * r) ^ 2 + (C * r - S * s) ^ 2 = (C ^ 2 + S ^ 2) * (s ^ 2 + r ^ 2) by ring,
        hCS, hsr]; norm_num)
    refine ⟨_, h1, ?_, ?_⟩
    · rw [h2]; nlinarith [mul_nonneg hS hr0, mul_le_mul_of_nonpos_left hs1 hC.le]
    · rw [h3, show (C * s + S * r) * s + (C * r - S * s) * r = C * (s ^ 2 + r ^ 2) by ring, hsr,
        mul_one]

lemma single_inner {d : ℕ} (i j : Fin d) :
    inner ℝ (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) =
      if i = j then (1 : ℝ) else 0 := by
  rw [EuclideanSpace.inner_single_left]
  simp

end CtxInvOpt.Offline.Pf20ea

open CtxInvOpt.Offline.Pf20ea Real in
open CtxInvOpt.Offline in
theorem solution {n d N : ℕ} (hn : 1 ≤ n) (hd : 2 ≤ d) :
    (∀ (Xs : Fin N → Set (EuclideanSpace ℝ (Fin n)))
        (fs : Fin N → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d))
        (xs : Fin N → EuclideanSpace ℝ (Fin n)),
        (∀ i, IsActionSet (Xs i)) → (∀ i, IsContext (fs i)) →
        ∀ c0 : EuclideanSpace ℝ (Fin d), c0 ∈ unitSphere d →
        (∀ i, xs i ∈ argminSet c0 (Xs i) (fs i)) →
        ∀ chat : EuclideanSpace ℝ (Fin d), IsCircumcenter (consistentSet Xs fs xs) chat →
        ∀ cstar ∈ consistentSet Xs fs xs,
        ∀ (X : Set (EuclideanSpace ℝ (Fin n)))
          (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d)),
          IsActionSet X → IsContext f →
          ∀ xpi ∈ argminSet chat X f, ∀ xstar ∈ argminSet cstar X f,
            inner ℝ (f xpi - f xstar) cstar ≤ regretCap (uncAngle (consistentSet Xs fs xs))) ∧
    (∀ abar ∈ Set.Icc (0 : ℝ) Real.pi,
      ∃ C : Set (EuclideanSpace ℝ (Fin d)), C ⊆ unitSphere d ∧ C.Nonempty ∧ uncAngle C = abar ∧
        ∀ pol : Set (EuclideanSpace ℝ (Fin n)) →
            (EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin n),
          (∀ X f, IsActionSet X → IsContext f → pol X f ∈ X) →
          ∃ cstar ∈ C, ∃ (X : Set (EuclideanSpace ℝ (Fin n)))
            (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d)),
            IsActionSet X ∧ IsContext f ∧
            ∃ xstar ∈ argminSet cstar X f,
              regretCap abar ≤ inner ℝ (f (pol X f) - f xstar) cstar) := by
  refine ⟨?_, ?_⟩
  · intro Xs fs xs _ _ c0 _ _ chat hchat cstar hcs X f hX hf xpi hxpi xstar hxs
    exact partA _ chat hchat cstar hcs (fun c hc => hc.1) X f hX hf xpi hxpi xstar hxs
  · intro abar habar
    -- orthonormal pair in `ℝ^d`
    set e : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ) with he_def
    set w : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single ⟨1, by omega⟩ (1 : ℝ) with hw_def
    have hee : inner ℝ e e = (1 : ℝ) := by rw [he_def, single_inner]; simp
    have hww : inner ℝ w w = (1 : ℝ) := by rw [hw_def, single_inner]; simp
    have hew : inner ℝ e w = (0 : ℝ) := by
      rw [he_def, hw_def, single_inner]; simp [Fin.ext_iff]
    have hwe : inner ℝ w e = (0 : ℝ) := by rw [real_inner_comm]; exact hew
    have norm_of : ∀ c : EuclideanSpace ℝ (Fin d), inner ℝ c c = (1 : ℝ) → ‖c‖ = 1 := by
      intro c hc
      rw [real_inner_self_eq_norm_sq] at hc
      have h0 : 0 ≤ ‖c‖ := norm_nonneg _
      nlinarith [sq_nonneg (‖c‖ - 1)]
    have he1 : ‖e‖ = 1 := norm_of e hee
    have hw1 : ‖w‖ = 1 := norm_of w hww
    set Cap : Set (EuclideanSpace ℝ (Fin d)) :=
      {c | c ∈ unitSphere d ∧ Real.cos abar ≤ inner ℝ c e} with hCap
    have heCap : e ∈ Cap := ⟨(mem_unitSphere_iff _).2 he1, by rw [hee]; exact Real.cos_le_one _⟩
    have hunc : uncAngle Cap = abar := by
      apply le_antisymm
      · have hb : BddBelow (Set.range fun chat : unitSphere d =>
            ⨆ c : Cap, vecAngle (c : EuclideanSpace ℝ (Fin d)) chat) :=
          ⟨0, by
            rintro _ ⟨x, rfl⟩
            exact Real.iSup_nonneg (fun _ => vecAngle_nonneg _ _)⟩
        refine (ciInf_le hb ⟨e, heCap.1⟩).trans ?_
        apply Real.iSup_le _ habar.1
        rintro ⟨c, hc1, hc2⟩
        show vecAngle c e ≤ abar
        rw [vecAngle_unit ((mem_unitSphere_iff _).1 hc1) he1]
        calc Real.arccos (inner ℝ c e) ≤ Real.arccos (Real.cos abar) := Real.antitone_arccos hc2
          _ = abar := Real.arccos_cos habar.1 habar.2
      · have : Nonempty (unitSphere d) := ⟨⟨e, heCap.1⟩⟩
        apply le_ciInf
        rintro ⟨chat, hch⟩
        have hch1 : ‖chat‖ = 1 := (mem_unitSphere_iff _).1 hch
        obtain ⟨c, hc1, hce, hcch⟩ := far e w chat hee hww hew hch1 (Real.cos abar)
          (Real.sin abar) (Real.cos_sq_add_sin_sq abar)
          (Real.sin_nonneg_of_nonneg_of_le_pi habar.1 habar.2)
        refine le_ciSup_of_le (bdd _ chat) ⟨c, ⟨(mem_unitSphere_iff _).2 hc1, hce⟩⟩ ?_
        show abar ≤ vecAngle c chat
        rw [vecAngle_unit hc1 hch1]
        calc abar = Real.arccos (Real.cos abar) := (Real.arccos_cos habar.1 habar.2).symm
          _ ≤ Real.arccos (inner ℝ c chat) := Real.antitone_arccos hcch
    refine ⟨Cap, fun c hc => hc.1, ⟨e, heCap⟩, hunc, ?_⟩
    intro pol hpol
    -- the two test costs `C' e ± S' w`
    set C' : ℝ := if abar < π / 2 then Real.cos abar else 0 with hC'
    set S' : ℝ := if abar < π / 2 then Real.sin abar else 1 with hS'
    have hCS : C' ^ 2 + S' ^ 2 = 1 := by
      rw [hC', hS']; split_ifs
      · exact Real.cos_sq_add_sin_sq abar
      · norm_num
    have hcosC : Real.cos abar ≤ C' := by
      rw [hC']; split_ifs with h
      · exact le_rfl
      · exact Real.cos_nonpos_of_pi_div_two_le_of_le (not_lt.mp h) (by linarith [habar.2, Real.pi_pos])
    have hS0 : 0 ≤ S' := by
      rw [hS']; split_ifs
      · exact Real.sin_nonneg_of_nonneg_of_le_pi habar.1 habar.2
      · norm_num
    have hcap : regretCap abar = S' := by
      unfold regretCap; rw [hS']
    set cp : EuclideanSpace ℝ (Fin d) := C' • e + S' • w with hcp
    set cm : EuclideanSpace ℝ (Fin d) := C' • e + (-S') • w with hcm
    have inner_e : ∀ a b : ℝ, inner ℝ (a • e + b • w) e = a := by
      intro a b; rw [inner_add_left, inner_smul_left, inner_smul_left, hee, hwe]; simp
    have inner_w : ∀ a b : ℝ, inner ℝ w (a • e + b • w) = b := by
      intro a b; rw [inner_add_right, inner_smul_right, inner_smul_right, hww, hwe]; simp
    have inner_self : ∀ a b : ℝ, inner ℝ (a • e + b • w) (a • e + b • w) = a ^ 2 + b ^ 2 := by
      intro a b
      rw [inner_add_left, inner_add_right, inner_add_right, inner_smul_left, inner_smul_right,
        inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right, inner_smul_left,
        inner_smul_right, hee, hww, hew, hwe]
      simp; ring
    have mem_cap : ∀ b : ℝ, C' ^ 2 + b ^ 2 = 1 → C' • e + b • w ∈ Cap := by
      intro b hb
      refine ⟨(mem_unitSphere_iff _).2 (norm_of _ (by rw [inner_self]; exact hb)), ?_⟩
      rw [inner_e]; exact hcosC
    have hcpC : cp ∈ Cap := mem_cap S' hCS
    have hcmC : cm ∈ Cap := mem_cap (-S') (by nlinarith)
    -- the action set `{0, x1}` and context `f x = ⟪x1, x⟫ • w`
    set x1 : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ) with hx1
    have hx11 : inner ℝ x1 x1 = (1 : ℝ) := by rw [hx1, single_inner]; simp
    have hx1n : ‖x1‖ = 1 := by
      rw [real_inner_self_eq_norm_sq] at hx11
      have h0 : 0 ≤ ‖x1‖ := norm_nonneg _
      nlinarith [sq_nonneg (‖x1‖ - 1)]
    set X : Set (EuclideanSpace ℝ (Fin n)) := {0, x1} with hX
    set f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) :=
      fun x => (inner ℝ x1 x) • w with hf
    have hXa : IsActionSet X := by
      refine ⟨⟨0, by simp [hX]⟩, (Set.toFinite X).isCompact, ?_⟩
      rw [hX, Metric.diam_pair, dist_comm, dist_zero_right, hx1n]
    have hfc : IsContext f := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [dist_eq_norm, dist_eq_norm, hf]
      simp only
      rw [← sub_smul, ← inner_sub_right, norm_smul, hw1, mul_one, Real.norm_eq_abs]
      simp only [NNReal.coe_one, one_mul]
      calc |inner ℝ x1 (x - y)| ≤ ‖x1‖ * ‖x - y‖ := abs_real_inner_le_norm _ _
        _ = ‖x - y‖ := by rw [hx1n, one_mul]
    have hf0 : f 0 = 0 := by simp [hf]
    have hf1 : f x1 = w := by simp only [hf]; rw [hx11, one_smul]
    rcases hpol X f hXa hfc with h | h
    · -- policy plays `0`: adversary takes `cm`, optimum `x1`
      refine ⟨cm, hcmC, X, f, hXa, hfc, x1, ⟨by simp [hX], ?_⟩, ?_⟩
      · intro y hy
        rcases hy with rfl | rfl
        · rw [hf0, hf1, inner_zero_left, hcm, inner_w]; linarith
        · exact le_rfl
      · rw [h, hf0, hf1, zero_sub, inner_neg_left, hcm, inner_w, hcap]; simp
    · have h' : pol X f = x1 := h
      refine ⟨cp, hcpC, X, f, hXa, hfc, 0, ⟨by simp [hX], ?_⟩, ?_⟩
      · intro y hy
        rcases hy with rfl | rfl
        · exact le_rfl
        · rw [hf0, hf1, inner_zero_left, hcp, inner_w]; exact hS0
      · rw [h', hf0, hf1, sub_zero, hcp, inner_w, hcap]
