-- Prove2me | solution 1 for CtxInvOpt.PolyCone.eqB9_circum_in_duality
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T08:04:52.513081+00:00
-- url     : https://prove2.me/submissions/f32ae810-087a-4171-b704-79800f9be1ec

import Mathlib
import Definitions.Def_CtxInvOpt_PolyCone_Cones
import Definitions.Def_dualCone

open CtxInvOpt.PolyCone CtxInvOpt.Offline

theorem solution {p : ℕ} (K : Set (EuclideanSpace ℝ (Fin p)))
    (hclosed : IsClosed K) (hconv : Convex ℝ K)
    (hcone : ∀ x ∈ K, ∀ t : ℝ, 0 ≤ t → t • x ∈ K)
    (hpointed : ∀ x ∈ K, -x ∈ K → x = 0) (hne : ∃ x ∈ K, x ≠ 0) :
    circumradius K ^ 2 + inradius (ConvexOptimization.dualCone K) ^ 2 = 1 := by
  set KS : Set (EuclideanSpace ℝ (Fin p)) := K ∩ Metric.sphere 0 1 with hKS
  obtain ⟨x1, hx1K, hx1ne⟩ := hne
  have hx1pos : 0 < ‖x1‖ := norm_pos_iff.mpr hx1ne
  -- normalization
  have hnorm : ∀ c ∈ K, c ≠ 0 → ‖c‖⁻¹ • c ∈ KS := by
    intro c hc hc0
    refine ⟨hcone c hc _ (by positivity), ?_⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_pos_iff.mpr hc0).ne']
  have hKSne : KS.Nonempty := ⟨_, hnorm x1 hx1K hx1ne⟩
  have hKSnorm : ∀ k ∈ KS, ‖k‖ = 1 := fun k hk => mem_sphere_zero_iff_norm.mp hk.2
  have : Nonempty KS := hKSne.to_subtype
  have hKScpt : IsCompact KS := (isCompact_sphere (0 : (EuclideanSpace ℝ (Fin p))) 1).inter_left hclosed
  -- the support function m(u) = min_{k ∈ K, ‖k‖ = 1} ⟪k, u⟫
  set m : (EuclideanSpace ℝ (Fin p)) → ℝ := fun u => ⨅ k : KS, inner ℝ (k : (EuclideanSpace ℝ (Fin p))) u with hmdef
  have hbdd : ∀ u : (EuclideanSpace ℝ (Fin p)), BddBelow (Set.range fun k : KS => inner ℝ (k : (EuclideanSpace ℝ (Fin p))) u) := by
    intro u
    refine ⟨-‖u‖, ?_⟩
    rintro _ ⟨k, rfl⟩
    have h1 := abs_real_inner_le_norm (k : (EuclideanSpace ℝ (Fin p))) u
    rw [hKSnorm k k.2, one_mul] at h1
    exact (abs_le.mp h1).1
  have hm_le : ∀ u, ∀ k ∈ KS, m u ≤ inner ℝ k u := fun u k hk =>
    ciInf_le (hbdd u) (⟨k, hk⟩ : KS)
  have hm_att : ∀ u, ∃ k0 ∈ KS, m u = inner ℝ k0 u := by
    intro u
    obtain ⟨k0, hk0, hmin⟩ := hKScpt.exists_isMinOn hKSne
      ((continuous_id.inner continuous_const).continuousOn (s := KS) (f := fun k : (EuclideanSpace ℝ (Fin p)) => inner ℝ k u))
    refine ⟨k0, hk0, le_antisymm (hm_le u k0 hk0) (le_ciInf fun k => ?_)⟩
    exact (isMinOn_iff.mp hmin) k k.2
  have hm_cone : ∀ u, ∀ c ∈ K, m u * ‖c‖ ≤ inner ℝ c u := by
    intro u c hc
    by_cases hc0 : c = 0
    · subst hc0; simp
    · have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
      have h1 := hm_le u _ (hnorm c hc hc0)
      rw [real_inner_smul_left] at h1
      have : inner ℝ c u = ‖c‖ * (‖c‖⁻¹ * inner ℝ c u) := by field_simp
      rw [this]
      nlinarith
  -- m is 1-Lipschitz, hence continuous
  have hmcont : Continuous m := by
    refine (LipschitzWith.of_le_add (fun u v => ?_)).continuous
    obtain ⟨k0, hk0, hv⟩ := hm_att v
    have h1 := hm_le u k0 hk0
    have h2 : inner ℝ k0 u = inner ℝ k0 v + inner ℝ k0 (u - v) := by
      rw [inner_sub_right]; ring
    have h3 : inner ℝ k0 (u - v) ≤ ‖u - v‖ := by
      have := real_inner_le_norm k0 (u - v)
      rwa [hKSnorm k0 hk0, one_mul] at this
    rw [dist_eq_norm]
    linarith
  -- a unit vector maximizing m
  have hSne : (Metric.sphere (0 : (EuclideanSpace ℝ (Fin p))) 1).Nonempty := ⟨_, (hnorm x1 hx1K hx1ne).2⟩
  obtain ⟨u0, hu0S, hmax'⟩ := (isCompact_sphere (0 : (EuclideanSpace ℝ (Fin p))) 1).exists_isMaxOn hSne hmcont.continuousOn
  have hmax : ∀ u ∈ Metric.sphere (0 : (EuclideanSpace ℝ (Fin p))) 1, m u ≤ m u0 := fun u hu => (isMaxOn_iff.mp hmax') u hu
  have hu0n : ‖u0‖ = 1 := mem_sphere_zero_iff_norm.mp hu0S
  -- separation: the dual cone contains a unit vector
  have hsep : ∃ u ∈ Metric.sphere (0 : (EuclideanSpace ℝ (Fin p))) 1, 0 ≤ m u := by
    let C : ProperCone ℝ (EuclideanSpace ℝ (Fin p)) :=
      { carrier := K
        add_mem' := by
          intro x y hx hy
          have hmid := hconv hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
            (by norm_num)
          have := hcone _ hmid 2 (by norm_num)
          convert this using 1
          rw [smul_add, smul_smul, smul_smul]; norm_num
        zero_mem' := by
          have := hcone x1 hx1K 0 le_rfl
          simpa using this
        smul_mem' := by
          intro c x hx
          exact hcone x hx (c : ℝ) c.2
        isClosed' := hclosed }
    have hnot : -x1 ∉ C := fun h => hx1ne (hpointed x1 hx1K h)
    obtain ⟨y, hy, hyneg⟩ := C.hyperplane_separation' hnot
    have hy0 : y ≠ 0 := by rintro rfl; simp at hyneg
    have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    refine ⟨‖y‖⁻¹ • y, ?_, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hypos.ne']
    · obtain ⟨k0, hk0, hk⟩ := hm_att (‖y‖⁻¹ • y)
      rw [hk, real_inner_smul_right]
      exact mul_nonneg (by positivity) (hy k0 hk0.1)
  have hM0 : 0 ≤ m u0 := by
    obtain ⟨u, hu, hmu⟩ := hsep; exact hmu.trans (hmax u hu)
  have hM1 : m u0 ≤ 1 := by
    obtain ⟨k, hk⟩ := hKSne
    have := hm_le u0 k hk
    have h2 := real_inner_le_norm k u0
    rw [hKSnorm k hk, hu0n] at h2
    linarith
  -- the angle part: sup_c θ(c,u) = arccos (m u) for unit u
  have hvec_le_pi : ∀ c u : (EuclideanSpace ℝ (Fin p)), vecAngle c u ≤ Real.pi := by
    intro c u; unfold vecAngle; split_ifs
    · exact Real.pi_pos.le
    · exact Real.arccos_le_pi _
  have hvec_nonneg : ∀ c u : (EuclideanSpace ℝ (Fin p)), 0 ≤ vecAngle c u := by
    intro c u; unfold vecAngle; split_ifs
    · exact le_rfl
    · exact Real.arccos_nonneg _
  have hPhi : ∀ u ∈ Metric.sphere (0 : (EuclideanSpace ℝ (Fin p))) 1,
      (⨆ c : K, vecAngle (c : (EuclideanSpace ℝ (Fin p))) u) = Real.arccos (m u) := by
    intro u hu
    have hun : ‖u‖ = 1 := mem_sphere_zero_iff_norm.mp hu
    apply le_antisymm
    · refine Real.iSup_le (fun c => ?_) (Real.arccos_nonneg _)
      unfold vecAngle
      split_ifs with h0
      · exact Real.arccos_nonneg _
      · rw [not_or] at h0
        apply Real.arccos_le_arccos
        have hpos : 0 < ‖(c : (EuclideanSpace ℝ (Fin p)))‖ := norm_pos_iff.mpr h0.1
        rw [hun, mul_one, le_div_iff₀ hpos]
        exact hm_cone u c c.2
    · obtain ⟨k0, hk0, hk⟩ := hm_att u
      refine le_ciSup_of_le ⟨Real.pi, ?_⟩ (⟨k0, hk0.1⟩ : K) ?_
      · rintro _ ⟨c, rfl⟩; exact hvec_le_pi _ _
      · have hk0n := hKSnorm k0 hk0
        have hk00 : k0 ≠ 0 := by intro h; rw [h, norm_zero] at hk0n; norm_num at hk0n
        have hu00 : u ≠ 0 := by intro h; rw [h, norm_zero] at hun; norm_num at hun
        unfold vecAngle
        rw [if_neg (by simp [hk00, hu00]), hk0n, hun, hk]
        simp
  have : Nonempty (unitSphere p) := ⟨⟨u0, hu0S⟩⟩
  have hangle : uncAngle K = Real.arccos (m u0) := by
    unfold uncAngle
    apply le_antisymm
    · refine (ciInf_le ⟨0, ?_⟩ (⟨u0, hu0S⟩ : unitSphere p)).trans (hPhi u0 hu0S).le
      rintro _ ⟨u, rfl⟩
      exact Real.iSup_nonneg (fun c => hvec_nonneg _ _)
    · refine le_ciInf (fun u => ?_)
      rw [hPhi u u.2]
      exact Real.arccos_le_arccos (hmax u u.2)
  -- the inradius part
  set D := ConvexOptimization.dualCone K with hD
  have hdist : ∀ x ∈ Metric.sphere (0 : (EuclideanSpace ℝ (Fin p))) 1, x ∈ D →
      Metric.infDist x (frontier D) = m x := by
    intro x hxS hxD
    obtain ⟨k0, hk0, hk⟩ := hm_att x
    have hk0n := hKSnorm k0 hk0
    have hmx0 : 0 ≤ m x := by rw [hk]; exact hxD k0 hk0.1
    set z := x - m x • k0 with hz
    have hzD : z ∈ D := by
      intro c hc
      have h1 := hm_cone x c hc
      have h2 := real_inner_le_norm c k0
      rw [hk0n, mul_one] at h2
      rw [hz, inner_sub_right, real_inner_smul_right]
      nlinarith
    have hzint : z ∉ interior D := by
      intro hzi
      rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hzi
      obtain ⟨ε, hε, hball⟩ := hzi
      have hw : z - (ε / 2) • k0 ∈ Metric.ball z ε := by
        rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, hk0n,
          Real.norm_eq_abs, abs_of_pos (by positivity)]
        linarith
      have := hball hw k0 hk0.1
      rw [hz, inner_sub_right, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq, hk0n, ← hk] at this
      nlinarith
    have hzfr : z ∈ frontier D := ⟨subset_closure hzD, hzint⟩
    apply le_antisymm
    · calc Metric.infDist x (frontier D) ≤ dist x z := Metric.infDist_le_dist_of_mem hzfr
        _ = m x := by
          rw [dist_eq_norm, hz, sub_sub_cancel, norm_smul, hk0n, Real.norm_eq_abs,
            abs_of_nonneg hmx0, mul_one]
    · rw [Metric.le_infDist ⟨z, hzfr⟩]
      intro y hy
      by_contra hlt
      push Not at hlt
      have hballD : Metric.ball x (m x) ⊆ D := by
        intro w hw c hc
        rw [Metric.mem_ball, dist_eq_norm] at hw
        have h1 := hm_cone x c hc
        have h2 := abs_real_inner_le_norm c (w - x)
        have h3 : inner ℝ c w = inner ℝ c x + inner ℝ c (w - x) := by
          rw [inner_sub_right]; ring
        have h4 := (abs_le.mp h2).1
        have h5 : ‖c‖ * ‖w - x‖ ≤ ‖c‖ * m x :=
          mul_le_mul_of_nonneg_left hw.le (norm_nonneg c)
        nlinarith
      have hyb : y ∈ Metric.ball x (m x) := by
        rw [Metric.mem_ball, dist_comm]; exact hlt
      exact hy.2 (interior_maximal hballD Metric.isOpen_ball hyb)
  have hu0D : u0 ∈ D := by
    intro c hc
    have := hm_cone u0 c hc
    nlinarith [norm_nonneg c]
  have hrad : inradius D = m u0 := by
    unfold inradius
    have hf : ∀ x : (unitSphere p ∩ D : Set (EuclideanSpace ℝ (Fin p))),
        Metric.infDist (x : (EuclideanSpace ℝ (Fin p))) (frontier D) = m x := fun x => hdist x x.2.1 x.2.2
    have : Nonempty (unitSphere p ∩ D : Set (EuclideanSpace ℝ (Fin p))) := ⟨⟨u0, hu0S, hu0D⟩⟩
    apply le_antisymm
    · exact ciSup_le (fun x => (hf x).le.trans (hmax x x.2.1))
    · refine le_ciSup_of_le ⟨m u0, ?_⟩ (⟨u0, hu0S, hu0D⟩ : (unitSphere p ∩ D : Set (EuclideanSpace ℝ (Fin p)))) ?_
      · rintro _ ⟨x, rfl⟩; exact (hf x).le.trans (hmax x x.2.1)
      · exact (hf ⟨u0, hu0S, hu0D⟩).ge
  unfold circumradius
  rw [hangle, hrad, Real.sin_arccos, Real.sq_sqrt (by nlinarith)]
  ring
