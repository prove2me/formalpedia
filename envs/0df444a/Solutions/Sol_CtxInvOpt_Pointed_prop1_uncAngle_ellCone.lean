-- Prove2me | solution 1 for CtxInvOpt.Pointed.prop1_uncAngle_ellCone
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T03:49:30.948147+00:00
-- url     : https://prove2.me/submissions/4a16e796-827e-4a7a-8ac9-016cc7d0e600

import Mathlib
import Definitions.Def_CtxInvOpt_Pointed_EllCone

open Matrix CtxInvOpt.Pointed

namespace P1

lemma inner_eq_dot {k : ℕ} (x y : EuclideanSpace ℝ (Fin k)) :
    inner ℝ x y = (WithLp.ofLp x) ⬝ᵥ (WithLp.ofLp y) := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]

lemma dot_mulVec_left {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (x y : Fin k → ℝ) :
    (A *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (Aᵀ *ᵥ y) := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]

lemma dot_rotU {k : ℕ} (U : Matrix (Fin k) (Fin k) ℝ) (hU : U ∈ orthogonalGroup (Fin k) ℝ)
    (x y : Fin k → ℝ) : (U *ᵥ x) ⬝ᵥ (U *ᵥ y) = x ⬝ᵥ y := by
  have h2 : Uᵀ * U = 1 := by simpa using (mem_orthogonalGroup_iff' (Fin k) ℝ).1 hU
  rw [dot_mulVec_left, mulVec_mulVec, h2, one_mulVec]

lemma dot_rotUt {k : ℕ} (U : Matrix (Fin k) (Fin k) ℝ) (hU : U ∈ orthogonalGroup (Fin k) ℝ)
    (x y : Fin k → ℝ) : (Uᵀ *ᵥ x) ⬝ᵥ (Uᵀ *ᵥ y) = x ⬝ᵥ y := by
  have h1 : U * Uᵀ = 1 := by simpa using (mem_orthogonalGroup_iff (Fin k) ℝ).1 hU
  rw [dot_mulVec_left, mulVec_mulVec, transpose_transpose, h1, one_mulVec]

lemma norm_sq_eq_dot {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) :
    ‖x‖ ^ 2 = (WithLp.ofLp x) ⬝ᵥ (WithLp.ofLp x) := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_dot]

lemma vecAngle_nonneg {d : ℕ} (c chat : EuclideanSpace ℝ (Fin d)) :
    0 ≤ CtxInvOpt.Offline.vecAngle c chat := by
  unfold CtxInvOpt.Offline.vecAngle; split_ifs
  · exact le_rfl
  · exact Real.arccos_nonneg _

lemma vecAngle_le_pi {d : ℕ} (c chat : EuclideanSpace ℝ (Fin d)) :
    CtxInvOpt.Offline.vecAngle c chat ≤ Real.pi := by
  unfold CtxInvOpt.Offline.vecAngle; split_ifs
  · exact Real.pi_pos.le
  · exact Real.arccos_le_pi _

lemma vecAngle_eq_angle {d : ℕ} (c chat : EuclideanSpace ℝ (Fin d)) (hc : c ≠ 0) (hh : chat ≠ 0) :
    CtxInvOpt.Offline.vecAngle c chat = InnerProductGeometry.angle c chat := by
  unfold CtxInvOpt.Offline.vecAngle InnerProductGeometry.angle
  rw [if_neg (by tauto)]

end P1

open P1 in
theorem solution {m : ℕ} (hm : 1 ≤ m) (w : Fin m → ℝ) (hw : ∀ i, 0 < w i)
    (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin (m + 1)) ℝ) :
    CtxInvOpt.Offline.uncAngle (ellCone w U) = Real.arctan (Real.sqrt (lamMax w)) := by
  have : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  obtain ⟨k, hk⟩ := Finite.exists_max w
  have hlam : lamMax w = w k :=
    le_antisymm (ciSup_le hk) (le_ciSup (Set.finite_range w).bddAbove k)
  set lam := lamMax w with hlamdef
  have hlampos : 0 < lam := by rw [hlam]; exact hw k
  set θ := Real.arctan (Real.sqrt lam) with hθdef
  have hθ0 : 0 ≤ θ := by rw [hθdef]; exact Real.arctan_nonneg.2 (Real.sqrt_nonneg _)
  have hθlt : θ < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  set chat : EuclideanSpace ℝ (Fin (m+1)) := axisVec U with hchat
  -- upper bound at the axis
  have hchatv : WithLp.ofLp chat = U *ᵥ (Pi.single 0 1 : Fin (m+1) → ℝ) := by
    ext i; simp [hchat, axisVec, mulVec, dotProduct, Pi.single_apply]
  have hchatn : ‖chat‖ = 1 := by
    have := norm_sq_eq_dot chat
    rw [hchatv, dot_rotU U hU, dotProduct_single] at this
    simp at this
    rcases this with h | h
    · exact h
    · linarith [norm_nonneg chat]
  have hchat0 : chat ≠ 0 := by intro h; rw [h, norm_zero] at hchatn; exact zero_ne_one hchatn
  have hcosθ : Real.cos θ = 1 / Real.sqrt (1 + lam) := by
    rw [hθdef, Real.cos_arctan, Real.sq_sqrt hlampos.le]
  have hsup_axis : ∀ c ∈ ellCone w U, CtxInvOpt.Offline.vecAngle c chat ≤ θ := by
    rintro c ⟨hy0, hy1⟩
    by_cases hc : c = 0
    · simp [CtxInvOpt.Offline.vecAngle, hc, hθ0]
    set y := rotCoord U c with hydef
    have hinner : inner ℝ c chat = y 0 := by
      rw [inner_eq_dot, hchatv, dotProduct_comm, dot_mulVec_left, dotProduct_comm, dotProduct_single,
        mul_one]
      rfl
    have hnorm : ‖c‖ ^ 2 = y 0 ^ 2 + ∑ i : Fin m, y i.succ ^ 2 := by
      rw [norm_sq_eq_dot, ← dot_rotUt U hU]
      simp [hydef, rotCoord, dotProduct, Fin.sum_univ_succ, sq]
    have htail : ∑ i : Fin m, y i.succ ^ 2 ≤ lam * y 0 ^ 2 := by
      have : ∑ i : Fin m, y i.succ ^ 2 ≤ ∑ i : Fin m, lam * (y i.succ ^ 2 / w i) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have hwi := hw i
        have hle : w i ≤ lam := by rw [hlam]; exact hk i
        rw [show lam * (y i.succ ^ 2 / w i) = (lam / w i) * y i.succ ^ 2 by ring]
        have : 1 ≤ lam / w i := by rw [le_div_iff₀ hwi]; linarith
        nlinarith [sq_nonneg (y i.succ)]
      rw [← Finset.mul_sum] at this
      have := mul_le_mul_of_nonneg_left hy1 hlampos.le
      linarith
    have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc
    have hcn2 : ‖c‖ ^ 2 ≤ (1 + lam) * y 0 ^ 2 := by rw [hnorm]; linarith
    have hcle : ‖c‖ ≤ Real.sqrt (1 + lam) * y 0 := by
      rw [← Real.sqrt_sq hcpos.le, ← Real.sqrt_sq hy0, ← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt hcn2
    have hs : 0 < Real.sqrt (1 + lam) := Real.sqrt_pos.2 (by positivity)
    rw [CtxInvOpt.Offline.vecAngle, if_neg (by tauto), hinner, hchatn, mul_one]
    calc Real.arccos (y 0 / ‖c‖) ≤ Real.arccos (Real.cos θ) := by
          apply Real.arccos_le_arccos
          rw [hcosθ, div_le_div_iff₀ hs hcpos]
          linarith
      _ = θ := Real.arccos_cos hθ0 (by linarith [Real.pi_pos])
  -- the two extreme rays
  set vp : Fin (m+1) → ℝ := Fin.cons 1 (Pi.single k (Real.sqrt lam)) with hvp
  set vm : Fin (m+1) → ℝ := Fin.cons 1 (Pi.single k (-Real.sqrt lam)) with hvm
  set cp : EuclideanSpace ℝ (Fin (m+1)) := WithLp.toLp 2 (U *ᵥ vp) with hcp
  set cm : EuclideanSpace ℝ (Fin (m+1)) := WithLp.toLp 2 (U *ᵥ vm) with hcm
  have hUtU : Uᵀ * U = 1 := by simpa using (mem_orthogonalGroup_iff' (Fin (m+1)) ℝ).1 hU
  have hsq : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hlampos.le
  have hmem : ∀ s : ℝ, s ^ 2 = lam →
      WithLp.toLp 2 (U *ᵥ (Fin.cons 1 (Pi.single k s) : Fin (m+1) → ℝ)) ∈ ellCone w U := by
    intro s hs
    have hrot : rotCoord U (WithLp.toLp 2 (U *ᵥ (Fin.cons 1 (Pi.single k s) : Fin (m+1) → ℝ))) =
        Fin.cons 1 (Pi.single k s) := by
      unfold rotCoord; simp only [WithLp.ofLp_toLp]; rw [mulVec_mulVec, hUtU, one_mulVec]
    refine ⟨?_, ?_⟩
    · rw [hrot]; simp
    · rw [hrot]
      simp only [Fin.cons_zero, Fin.cons_succ, one_pow]
      rw [Finset.sum_eq_single k (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
      simp only [Pi.single_eq_same]
      rw [hs, hlam, div_self (hw k).ne']
  have hcpm : cp ∈ ellCone w U := hmem _ hsq
  have hcmm : cm ∈ ellCone w U := hmem _ (by rw [neg_sq, hsq])
  have hdotv : ∀ s t : ℝ, (Fin.cons 1 (Pi.single k s) : Fin (m+1) → ℝ) ⬝ᵥ
      (Fin.cons 1 (Pi.single k t) : Fin (m+1) → ℝ) = 1 + s * t := by
    intro s t
    simp only [dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_one]
    rw [Finset.sum_eq_single k (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
    simp
  have hnp : ‖cp‖ ^ 2 = 1 + lam := by
    rw [norm_sq_eq_dot, hcp, WithLp.ofLp_toLp, dot_rotU U hU, hvp, hdotv, ← sq, hsq]
  have hnm : ‖cm‖ ^ 2 = 1 + lam := by
    rw [norm_sq_eq_dot, hcm, WithLp.ofLp_toLp, dot_rotU U hU, hvm, hdotv, neg_mul_neg, ← sq, hsq]
  have hipm : inner ℝ cp cm = 1 - lam := by
    rw [inner_eq_dot, hcp, hcm, WithLp.ofLp_toLp, WithLp.ofLp_toLp, dot_rotU U hU, hvp, hvm, hdotv]
    rw [mul_neg, ← sq, hsq]; ring
  have hcp0 : cp ≠ 0 := by intro h; rw [h, norm_zero] at hnp; linarith
  have hcm0 : cm ≠ 0 := by intro h; rw [h, norm_zero] at hnm; linarith
  have hnpe : ‖cp‖ = Real.sqrt (1 + lam) := by rw [← hnp, Real.sqrt_sq (norm_nonneg _)]
  have hnme : ‖cm‖ = Real.sqrt (1 + lam) := by rw [← hnm, Real.sqrt_sq (norm_nonneg _)]
  have hangle : InnerProductGeometry.angle cp cm = 2 * θ := by
    unfold InnerProductGeometry.angle
    rw [hipm, hnpe, hnme, Real.mul_self_sqrt (by positivity)]
    have hcos2 : Real.cos (2 * θ) = (1 - lam) / (1 + lam) := by
      rw [Real.cos_two_mul, hcosθ, div_pow, Real.sq_sqrt (by positivity)]
      field_simp; ring
    rw [← hcos2, Real.arccos_cos (by linarith) (by linarith)]
  have hlow : ∀ ch : EuclideanSpace ℝ (Fin (m+1)), ch ≠ 0 →
      θ ≤ max (CtxInvOpt.Offline.vecAngle cp ch) (CtxInvOpt.Offline.vecAngle cm ch) := by
    intro ch hch
    rw [vecAngle_eq_angle cp ch hcp0 hch, vecAngle_eq_angle cm ch hcm0 hch]
    have := InnerProductGeometry.angle_le_angle_add_angle cp ch cm
    rw [hangle, InnerProductGeometry.angle_comm ch cm] at this
    by_contra hcon
    replace hcon := lt_of_not_ge hcon
    have h1 := lt_of_le_of_lt (le_max_left _ _) hcon
    have h2 := lt_of_le_of_lt (le_max_right _ _) hcon
    linarith
  have hC0 : (0 : EuclideanSpace ℝ (Fin (m+1))) ∈ ellCone w U := by
    refine ⟨?_, ?_⟩ <;> simp [rotCoord]
  have hbdd : ∀ ch : EuclideanSpace ℝ (Fin (m+1)),
      BddAbove (Set.range fun c : ellCone w U => CtxInvOpt.Offline.vecAngle (c : EuclideanSpace ℝ (Fin (m+1))) ch) :=
    fun ch => ⟨Real.pi, by rintro _ ⟨x, rfl⟩; exact vecAngle_le_pi _ _⟩
  have hne : Nonempty (ellCone w U) := ⟨⟨0, hC0⟩⟩
  have hsphere : chat ∈ CtxInvOpt.Offline.unitSphere (m+1) := by
    simp [CtxInvOpt.Offline.unitSphere, hchatn]
  apply le_antisymm
  · unfold CtxInvOpt.Offline.uncAngle
    refine (ciInf_le ⟨0, ?_⟩ ⟨chat, hsphere⟩).trans ?_
    · rintro _ ⟨x, rfl⟩
      exact Real.iSup_nonneg (fun c => vecAngle_nonneg _ _)
    · exact ciSup_le (fun c => hsup_axis c.1 c.2)
  · unfold CtxInvOpt.Offline.uncAngle
    have : Nonempty (CtxInvOpt.Offline.unitSphere (m+1)) := ⟨⟨chat, hsphere⟩⟩
    refine le_ciInf (fun ch => ?_)
    have hch0 : (ch : EuclideanSpace ℝ (Fin (m+1))) ≠ 0 := by
      intro h
      have := ch.2
      simp [CtxInvOpt.Offline.unitSphere, h] at this
    have := hlow ch hch0
    rcases le_max_iff.1 this with h | h
    · exact h.trans (le_ciSup (hbdd ch) ⟨cp, hcpm⟩)
    · exact h.trans (le_ciSup (hbdd ch) ⟨cm, hcmm⟩)
