-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.fa_main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:09:27.523117+00:00
-- url     : https://prove2.me/submissions/45e796cc-a892-475e-aa7a-162e494eb419

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_mul_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_mul_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_psi_R
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_intK_eq_bx
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_bx_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_bx_mul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_bx_indep
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_bx_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_bx_equiv
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_bx_scale
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_sumU
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_fin_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_orbital_integral_two_blocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_GG_supp
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_fa_card_Pr
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_fa_ee_bij
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_fa_Hm_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_fa_sub_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_fa_lat
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_fa_mem_mulR
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_fa_inv_y
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_fa_ys_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_fa_ys_mem
import Theorems.Thm_Formalism_DoubleCosetMeasures_Final_simpleAdd
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_sUp_mem
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_simpleAdd
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_modK_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ} {ϖ : Kˣ} {L₀ Λ₀ : AddSubgroup K} {Q : Set K} {a b : ℕ}
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution (hD : LocalDatum K R ψ) (hC : Cst R ϖ L₀ Λ₀ Q a b) (hL₀ : IsLat L₀) {m : ℕ}
    (Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ)
    (hΦ : PhiHyp R (m + 1) L₀ Λ₀ Q Φ) (t c D' : Kˣ) (hD'Q : (D' : K) ∈ Q ∨ -(D' : K) ∈ Q) {b₁ : ℕ}
    (hI : InvP R ψ ϖ Φ m (D' : K) b₁) (htR : (t : K) ∈ R)
    (hLA : ∀ N : Pr (m + 1) → K,
      ∑ᶠ ξ : Fin m → KR R,
        Φ (m + 1) ((Hm (t : K) (c : K) (outV R ξ) (1 + EE N)).submatrix Fin.rev id) *
          ψ (lastE (outV R ξ) + sUp (1 + EE N)) =
      ψ (g0 (D' : K) (xs ((t : K) • N)) * ((t⁻¹ : Kˣ) : K)) *
        bx R (mulR R ((ϖ ^ b₁ : Kˣ) : K)) (Fin m)
          (fun τ => GG R ψ Φ (D' : K) (xs ((t : K) • N)) (ys ((t : K) • N) τ)))
    (Λ : AddSubgroup K) (hΛ : IsLat Λ)
    (hΛinv : LatInvN Λ (fun x : Fin m → K =>
      bx R (mulR R ((ϖ ^ b₁ : Kˣ) : K)) (Pr (m + 1)) (GG R ψ Φ (D' : K) x) *
        ψ (g0 (D' : K) x * ((t⁻¹ : Kˣ) : K)))) :
    omPhi R ψ (pt2 h0 m t c) Φ = ((((modK R (t : K)) ^ (m * (m + 1) / 2))⁻¹ : ℝ) : ℂ) *
      intK R Λ m (fun x : Fin m → K =>
        bx R (mulR R ((ϖ ^ b₁ : Kˣ) : K)) (Pr (m + 1)) (GG R ψ Φ (D' : K) x) *
          ψ (g0 (D' : K) x * ((t⁻¹ : Kˣ) : K))) := by
  have hA := hC.adic
  have htt : (t : K) * ((t⁻¹ : Kˣ) : K) = 1 := by simp
  set Λ₁ : AddSubgroup K := mulR R ((ϖ ^ b₁ : Kˣ) : K) with hΛ₁
  set Λt : AddSubgroup K := mulR R ((t * ϖ ^ b₁ : Kˣ) : K) with hΛt
  have hlat1 : IsLat Λ₁ := fa_lat hA _
  have hlatt : IsLat Λt := fa_lat hA _
  have hmemt : ∀ x : K, x ∈ Λt → ∃ r ∈ R, x = (t : K) * (ϖ : K) ^ b₁ * r := by
    intro x hx
    obtain ⟨r, hr, e⟩ := fa_mem_mulR.1 hx
    exact ⟨r, hr, by rw [e]; push_cast; ring⟩
  have hsmul : ∀ x : K, x ∈ Λ₁ → (t : K) * x ∈ Λt := by
    intro x hx
    obtain ⟨r, hr, e⟩ := fa_mem_mulR.1 hx
    exact fa_mem_mulR.2 ⟨r, hr, by rw [e]; push_cast; ring⟩
  set J : (Fin m → K) → (Pr (m + 1) → K) → ℂ := fun x y =>
    GG R ψ Φ (D' : K) x y * ψ (g0 (D' : K) x * ((t⁻¹ : Kˣ) : K)) with hJdef
  have hJ : ∀ (x l : Fin m → K) (y l' : Pr (m + 1) → K), (∀ k, l k ∈ Λt) → (∀ p, l' p ∈ Λt) →
      J (x + l) (y + l') = J x y := by
    intro x l y l' hl hl'
    obtain ⟨h1, h2⟩ := hI t htR x l y l' (fun k => hmemt _ (hl k)) (fun p => hmemt _ (hl' p))
    simp only [hJdef]
    by_cases h0 : GG R ψ Φ (D' : K) x y = 0
    · rw [h1, h0]; simp
    · obtain ⟨r, hr, e⟩ := h2 h0
      rw [h1]
      congr 1
      have : g0 (D' : K) (x + l) * ((t⁻¹ : Kˣ) : K) = g0 (D' : K) x * ((t⁻¹ : Kˣ) : K) + r := by
        linear_combination ((t⁻¹ : Kˣ) : K) * e + r * htt
      rw [this, AddChar.map_add_eq_mul, psi_R hD hr, mul_one]
  have hJ1 : ∀ (x : Fin m → K) (y l' : Pr (m + 1) → K), (∀ p, l' p ∈ Λ₁) → J x (y + l') = J x y := by
    intro x y l' hl'
    simp only [hJdef]
    rw [fa_inv_y hI x y l' hl']
  set k : Matrix (Fin (m + 1)) (Fin (m + 1)) K → ℂ := fun u =>
    ∑ᶠ ξ : Fin m → KR R, Φ (m + 1) ((Hm (t : K) (c : K) (outV R ξ) u).submatrix Fin.rev id) *
      ψ (lastE (outV R ξ) + sUp u) with hk
  set f : (Pr (m + 1) → K) → ℂ := fun n => bx R Λt (Fin m) (fun τ => J (xs n) (ys n τ)) with hf
  have hkf : ∀ N : Pr (m + 1) → K, k (1 + EE N) = f ((t : K) • N) := by
    intro N
    simp only [hk, hf]
    rw [hLA N, ← bx_mul_left]
    rw [bx_indep hD hlatt hlat1 (fun τ => J (xs ((t : K) • N)) (ys ((t : K) • N) τ))
      (by
        intro τ l hl
        have e : ys ((t : K) • N) (τ + l) = ys ((t : K) • N) τ + ys 0 l := by
          rw [← fa_ys_add, add_zero]
        show J _ (ys ((t : K) • N) (τ + l)) = _
        rw [e]
        have := hJ (xs ((t : K) • N)) 0 (ys ((t : K) • N) τ) (ys 0 l) (fun _ => Λt.zero_mem)
          (fa_ys_mem Λt 0 l (fun _ => Λt.zero_mem) hl)
        simpa using this)
      (by
        intro τ l hl
        have e : ys ((t : K) • N) (τ + l) = ys ((t : K) • N) τ + ys 0 l := by
          rw [← fa_ys_add, add_zero]
        show J _ (ys ((t : K) • N) (τ + l)) = _
        rw [e]
        exact hJ1 _ _ _ (fa_ys_mem Λ₁ 0 l (fun _ => Λ₁.zero_mem) hl))]
    exact bx_congr _ fun τ => by simp only [hJdef]; ring
  have hfinv : BInv Λt f := by
    intro n l hl
    simp only [hf]
    refine bx_congr _ fun τ => ?_
    have e : ys (n + l) τ = ys n τ + ys l 0 := by rw [← fa_ys_add, add_zero]
    rw [e]
    exact hJ (xs n) (xs l) _ _ (fun i => hl _) (fa_ys_mem Λt l 0 hl (fun _ => Λt.zero_mem))
  have hfinv' : BInv Λ₁ (fun N : Pr (m + 1) → K => f ((t : K) • N)) := by
    intro N l hl
    show f ((t : K) • (N + l)) = f ((t : K) • N)
    rw [smul_add]
    exact hfinv _ _ fun p => hsmul _ (hl p)
  have hU := sumU hD (m + 1) k (by
      intro u r hu hr hrI
      simp only [hk]
      refine finsum_congr fun ξ => ?_
      rw [fa_Hm_mul _ _ _ _ _ hr, fa_sub_mul, hΦ.1 _ 1 r (isLowUni_one K) (by
        intro i j; rw [Matrix.one_apply]; split_ifs; exacts [R.one_mem, R.zero_mem]) hr hrI,
        (Formalism.DoubleCosetMeasures.P.simpleAdd K (m + 1) u r).2 hu hr, ← add_assoc, AddChar.map_add_eq_mul _ _ (sUp r),
        psi_R hD (Formalism.DoubleCosetMeasures.P.sUp_mem R _ hrI), mul_one]) (by
      refine (fin_single hD (m + 1) (ϖ ^ a * t)).subset ?_
      intro q hq
      have hq' : k (sec_m (Quotient.out q)) ≠ 0 := hq
      have hu : IsUpUni (sec_m (Quotient.out q)) := (Quotient.out q).2
      obtain ⟨ξ, hξ⟩ : ∃ ξ : Fin m → KR R, Φ (m + 1) ((Hm (t : K) (c : K) (outV R ξ)
          (sec_m (Quotient.out q))).submatrix Fin.rev id) *
          ψ (lastE (outV R ξ) + sUp (sec_m (Quotient.out q))) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hq' (finsum_eq_zero_of_forall_eq_zero hcon)
      have h1 := hΦ.2.1 _ (left_ne_zero_of_mul hξ)
      intro i j
      have h3 : ((ϖ ^ a * t : Kˣ) : K) • sec_m (Quotient.out q) i j =
          (ϖ : K) ^ a * ((t : K) * sec_m (Quotient.out q) i j) := by
        push_cast; rw [smul_eq_mul, mul_assoc]
      show ((ϖ ^ a * t : Kˣ) : K) • sec_m (Quotient.out q) i j ∈ R
      rw [h3]
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · have : sec_m (Quotient.out q) (Fin.last m) j ∈ R := by
          by_cases hj : j = Fin.last m
          · rw [hj, hu.2]; exact R.one_mem
          · have h0 : sec_m (Quotient.out q) (Fin.last m) j = 0 :=
              hu.1 (lt_of_le_of_ne (Fin.le_last j) hj)
            exact Eq.mpr (congrArg (fun x => x ∈ R) h0) R.zero_mem
        exact R.mul_mem (R.pow_mem hA.mem a) (R.mul_mem htR this)
      · have h2 := hC.L0 _ (h1 (Fin.rev i'.succ) j)
        simpa [Hm, Bd] using h2) hlat1 (by
      intro N l hl
      show k (1 + EE (N + l)) = k (1 + EE N)
      rw [hkf, hkf]
      exact hfinv' N l hl)
  have hsc := bx_scale hD t hlatt hlat1 f hfinv hfinv'

  set Jh : (Fin m ⊕ Pr (m + 1) → K) → ℂ := fun v => J (fun i => v (Sum.inl i)) (fun p => v (Sum.inr p))
    with hJh
  have hsJh : BSupp L₀ Jh := by
    intro v hv
    have h0 : GG R ψ Φ (D' : K) (fun i => v (Sum.inl i)) (fun p => v (Sum.inr p)) ≠ 0 :=
      left_ne_zero_of_mul hv
    obtain ⟨h1, h2, -⟩ := GG_supp hC Φ hΦ D' hD'Q _ _ h0
    rintro (i | p)
    · exact (h1 i).1
    · exact h2 p
  have h7 := bx_sum hD (ι := Pr (m + 1)) (κ := Fin m) hlatt hL₀ (fun w => Jh (fun k => w (ee k))) (by
    intro w hw j
    obtain ⟨k, rfl⟩ := fa_ee_bij.2 j
    exact hsJh (fun k => w (ee k)) hw k)
  have h8 := bx_equiv (R := R) (Equiv.ofBijective ee (fa_ee_bij (m := m))).symm Λt Jh
  have h9 := bx_sum hD (ι := Fin m) (κ := Pr (m + 1)) hlatt hL₀ Jh hsJh
  have e7 : bx R Λt (Pr (m + 1)) f = bx R Λt (Fin m ⊕ Pr (m + 1)) Jh := by
    rw [h8]
    exact h7.symm
  have hF : ∀ x : Fin m → K, bx R Λ₁ (Pr (m + 1)) (GG R ψ Φ (D' : K) x) *
      ψ (g0 (D' : K) x * ((t⁻¹ : Kˣ) : K)) = bx R Λt (Pr (m + 1)) (J x) := by
    intro x
    rw [bx_indep hD hlatt hlat1 (J x) (by
        intro y l' hl'
        have := hJ x 0 y l' (fun _ => Λt.zero_mem) hl'
        simpa using this) (fun y l' hl' => hJ1 x y l' hl'), mul_comm, ← bx_mul_left]
    exact bx_congr _ fun y => by simp only [hJdef]; ring
  have e9 : bx R Λt (Fin m ⊕ Pr (m + 1)) Jh = bx R Λt (Fin m) (fun x => bx R Λt (Pr (m + 1)) (J x)) :=
    h9
  have e10 : bx R Λt (Fin m) (fun x => bx R Λt (Pr (m + 1)) (J x)) =
      intK R Λ m (fun x : Fin m → K => bx R Λ₁ (Pr (m + 1)) (GG R ψ Φ (D' : K) x) *
        ψ (g0 (D' : K) x * ((t⁻¹ : Kˣ) : K))) := by
    rw [intK_eq_bx, bx_congr _ hF]
    refine bx_indep hD hlatt hΛ _ ?_ ?_
    · intro x l hl
      refine bx_congr _ fun y => ?_
      have := hJ x l y 0 hl (fun _ => Λt.zero_mem)
      simpa using this
    · intro x l hl
      have := hΛinv x l hl
      simp only [hF] at this
      exact this
  have hP : 0 < modK R (t : K) := modK_pos hA.isOpen hA.isCompact t
  have hom := orbital_integral_two_blocks (ψ := ψ) hD m t c Φ (ϖ ^ a) hΦ.1 (by
    intro Z hZ i j
    have := hC.L0 _ (hΦ.2.1 Z hZ i j)
    simpa [Bd] using this)
  rw [hom]
  have e1 : (∑ᶠ q : upUniG K (m + 1) ⧸ intSub R (upUniG K (m + 1)), ∑ᶠ ξ : Fin m → KR R,
        Φ (m + 1) ((Hm (t : K) (c : K) (outV R ξ) (sec_m (Quotient.out q))).submatrix Fin.rev id) *
          ψ (lastE (outV R ξ) + sUp (sec_m (Quotient.out q)))) =
      bx R Λ₁ (Pr (m + 1)) (fun N => f ((t : K) • N)) := by
    rw [← bx_congr _ hkf]
    exact hU
  rw [e1, ← e10, ← e9, ← e7, ← hsc, fa_card_Pr]
  have hcard : (m + 1) * (m + 1 - 1) / 2 = m * (m + 1) / 2 := by
    rw [Nat.add_sub_cancel, mul_comm]
  rw [hcard]
  have hne : ((modK R (t : K) : ℝ) : ℂ) ^ (m * (m + 1) / 2) ≠ 0 := by
    exact_mod_cast (pow_pos hP _).ne'
  push_cast
  field_simp
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
