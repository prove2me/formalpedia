-- Prove2me | solution 1 for Formalism.L2.Pj.FundamentalDomainD5.d5_translation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:20:39.759811+00:00
-- url     : https://prove2.me/submissions/7e013005-29d9-40e6-9bb7-4093ce735165

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_DiscrMulIntegral
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_DotSelfEqSqNorm
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_ExistsBasisIn
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_LatticeZbasis
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_ThetaDotSelf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoveringRadiusStatement
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhiCMinF
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_FundamentalDomainD5
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_Phi_qsmul
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_Phi_sum
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_cover_round
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_discr_mul_integral
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_embVec_smul
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_exists_basis_in
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_finrank_cmType
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_h_qsmul_left
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_h_qsmul_right
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_h_smul_left
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_h_smul_right
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_h_sum_left
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_h_sum_right
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_lattice_zbasis
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_nondeg
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_phi_dot_self
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_rho_dot_self
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_rho_smul
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_rho_sub
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_rho_sum
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_theta_dot_self
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_trace_id
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PhiCMin_shortDual_holds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FundamentalDomainD5
open NumberField Matrix ComplexConjugate ReciprocityTheory.MultiplicativeHeights
namespace Formalism.L2.Pj.FundamentalDomainD5
theorem _root_.solution : ReciprocityTheory.ChartRestriction.G.FD.CoveringRadiusStatement := by
  intro K _ _ _ ι _ _ r p S σ Q L laStar hinj hcm hp hla hQ hform hL hSD hmin
  intro μ
  classical
  rcases Nat.eq_zero_or_pos r with hr0 | hr0
  · subst hr0
    refine ⟨fun w => ⟨0, L.zero_mem, ?_⟩, fun j => j.elim0, fun j => j.elim0,
      linearIndependent_empty_type, fun j => j.elim0⟩
    simp [normSq]
    positivity
  set f := Fintype.card ι with hf
  have hdeg : Module.finrank ℚ K = 2 * f := finrank_cmType σ hinj hcm
  set N := Module.finrank ℚ K * r with hN
  have hNpos : 0 < N := Nat.mul_pos Module.finrank_pos hr0
  obtain ⟨e, heL, heli, hecoord⟩ := lattice_zbasis L hL.1 hL.2
  have hcardN : Fintype.card (ι × Fin r × Fin 2) = N := by
    simp only [Fintype.card_prod, Fintype.card_fin, hN, hdeg, hf]
    ring
  let eqv : Fin N ≃ ι × Fin r × Fin 2 := (Fintype.equivFinOfCardEq hcardN).symm

  let A : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun k j => rho eqv (Phi σ Q (e j)) k
  have hAR : ∀ c : Fin N → ℝ, A *ᵥ c = ∑ j, c j • rho eqv (Phi σ Q (e j)) := by
    intro c
    funext k
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hAQ : ∀ c : Fin N → ℚ, A *ᵥ (fun j => ((c j : ℚ) : ℝ)) = rho eqv (Phi σ Q (∑ j, c j • e j)) := by
    intro c
    rw [hAR, Phi_sum, rho_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Phi_qsmul, rho_smul]

  let T : Matrix (Fin N) (Fin N) ℚ := Matrix.of fun k j => Algebra.trace ℚ K (S.h (e k) (e j))
  have hfinrank : Module.finrank ℚ (Fin r → K) = N := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hN,
      mul_comm]
  have : Nonempty (Fin N) := ⟨⟨0, hNpos⟩⟩
  let eB : Module.Basis (Fin N) ℚ (Fin r → K) :=
    basisOfLinearIndependentOfCardEqFinrank heli (by rw [Fintype.card_fin, hfinrank])
  have heB : ∀ j, eB j = e j := fun j => by simp [eB]
  have htrq : ∀ (q : ℚ) (z : K), Algebra.trace ℚ K ((q : K) * z) = q * Algebra.trace ℚ K z := by
    intro q z
    rw [← Rat.smul_def, map_smul, smul_eq_mul]
  have hTdet : T.det ≠ 0 := by
    intro h0
    obtain ⟨s, hs0, hs⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    set x := ∑ j, s j • e j with hx
    have hx0 : x ≠ 0 := by
      intro hx0
      exact hs0 (funext fun j => Fintype.linearIndependent_iff.1 heli s hx0 j)
    have hTx : ∀ k, Algebra.trace ℚ K (S.h (e k) x) = 0 := by
      intro k
      have h1 := congrFun hs k
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply, T] at h1
      rw [hx, h_sum_right, map_sum]
      simp only [h_qsmul_right, htrq]
      rw [← h1]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hall : ∀ v : Fin r → K, Algebra.trace ℚ K (S.h v x) = 0 := by
      intro v
      rw [← eB.sum_repr v, h_sum_left, map_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [heB, h_qsmul_left, htrq, hTx k, mul_zero]
    exact hx0 (nondeg σ Q hQ p S hform x hall)

  have hid : ∀ y v : Fin r → K, rho eqv (Theta p (Phi σ Q y)) ⬝ᵥ rho eqv (Phi σ Q v) =
      (1 / 2 : ℝ) * ((Algebra.trace ℚ K (S.h y v) : ℚ) : ℝ) := trace_id σ hinj hcm Q p S hform eqv
  have hAdet : A.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hTR : (T.map (Rat.castHom ℝ)).det ≠ 0 := by
      rw [show T.map (Rat.castHom ℝ) = (Rat.castHom ℝ).mapMatrix T from rfl, ← RingHom.map_det]
      exact (map_ne_zero _).2 hTdet
    apply hc0
    refine Matrix.eq_zero_of_mulVec_eq_zero hTR ?_
    funext k
    have h1 : rho eqv (Theta p (Phi σ Q (e k))) ⬝ᵥ (A *ᵥ c) = 0 := by rw [hc, dotProduct_zero]
    rw [hAR, dotProduct_sum] at h1
    simp only [dotProduct_smul, hid, smul_eq_mul] at h1
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply, Pi.zero_apply, Rat.coe_castHom, T]
    have h2 : ∑ j, ((Algebra.trace ℚ K (S.h (e k) (e j)) : ℚ) : ℝ) * c j =
        2 * ∑ j, c j * ((1 / 2 : ℝ) * ((Algebra.trace ℚ K (S.h (e k) (e j)) : ℚ) : ℝ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h2, h1, mul_zero]

  set dK : ℝ := |(NumberField.discr K : ℝ)| with hdK
  have hdpos : 0 < dK := abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero K)
  set μ' : ℝ := laStar / dK with hμ'
  have hμ'pos : 0 < μ' := div_pos hla hdpos
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.2 hAdet
  have hTTdet : Tᵀ.det ≠ 0 := by rw [Matrix.det_transpose]; exact hTdet
  have hAtdet : Aᵀ.det ≠ 0 := by rw [Matrix.det_transpose]; exact hAdet
  have hdual : ∀ t : Fin N → ℤ, t ≠ 0 →
      μ' ^ 2 ≤ ((A⁻¹)ᵀ *ᵥ fun i => (t i : ℝ)) ⬝ᵥ ((A⁻¹)ᵀ *ᵥ fun i => (t i : ℝ)) := by
    intro t ht
    set u := (A⁻¹)ᵀ *ᵥ fun i => (t i : ℝ) with hu
    have hAtu : Aᵀ *ᵥ u = fun i => (t i : ℝ) := by
      rw [hu, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul A hAu,
        Matrix.transpose_one, Matrix.one_mulVec]
    set tq : Fin N → ℚ := fun i => (t i : ℚ) with htq
    set s : Fin N → ℚ := (Tᵀ)⁻¹ *ᵥ ((2 : ℚ) • tq) with hs
    have hTs : Tᵀ *ᵥ s = (2 : ℚ) • tq := by
      rw [hs, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hTTdet), Matrix.one_mulVec]
    set y := ∑ j, s j • e j with hy
    have hyk : ∀ k, Algebra.trace ℚ K (S.h y (e k)) = 2 * (t k : ℚ) := by
      intro k
      have h1 := congrFun hTs k
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply, Pi.smul_apply,
        smul_eq_mul, htq, T] at h1
      rw [hy, h_sum_left, map_sum]
      simp only [h_qsmul_left, htrq]
      rw [← h1]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hAty : Aᵀ *ᵥ rho eqv (Theta p (Phi σ Q y)) = fun i => (t i : ℝ) := by
      funext k
      have h1 := hid y (e k)
      rw [dotProduct] at h1
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, A, Matrix.of_apply]
      rw [show (∑ m, rho eqv (Phi σ Q (e k)) m * rho eqv (Theta p (Phi σ Q y)) m) =
        ∑ m, rho eqv (Theta p (Phi σ Q y)) m * rho eqv (Phi σ Q (e k)) m from
        Finset.sum_congr rfl fun m _ => mul_comm _ _, h1, hyk k]
      push_cast
      ring
    have hu' : rho eqv (Theta p (Phi σ Q y)) = u := by
      have h1 : Aᵀ *ᵥ (rho eqv (Theta p (Phi σ Q y)) - u) = 0 := by
        rw [Matrix.mulVec_sub, hAty, hAtu, sub_self]
      exact sub_eq_zero.1 (Matrix.eq_zero_of_mulVec_eq_zero hAtdet h1)
    have hint : ∀ v ∈ L, ∃ n : ℤ, Algebra.trace ℚ K (S.h y v) = n := by
      intro v hv
      obtain ⟨n, hn⟩ := hecoord v hv
      refine ⟨∑ k, n k * (2 * t k), ?_⟩
      rw [hn, h_sum_right, map_sum]
      push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [h_qsmul_right, htrq, hyk k]
    have hdy : ((NumberField.discr K : ℤ) : K) • y ∈ L := by
      refine hSD.2 _ fun v hv => ?_
      have hz : ∀ a : 𝓞 K, ∃ n : ℤ, Algebra.trace ℚ K (S.h y v * a) = n := by
        intro a
        have hav : (a : K) • v ∈ L := L.smul_mem a hv
        obtain ⟨n, hn⟩ := hint _ hav
        refine ⟨n, ?_⟩
        rw [mul_comm, ← h_smul_right, hn]
      have hI := discr_mul_integral (S.h y v) hz
      refine ⟨⟨S.h (((NumberField.discr K : ℤ) : K) • y) v, ?_⟩, rfl⟩
      rw [h_smul_left, map_intCast]
      exact hI
    have hy0 : y ≠ 0 := by
      intro hy0
      have hs0 : s = 0 := funext fun j => Fintype.linearIndependent_iff.1 heli s hy0 j
      apply ht
      funext i
      have h1 := congrFun hTs i
      rw [hs0, Matrix.mulVec_zero] at h1
      simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul, htq] at h1
      have h2 : (t i : ℚ) = 0 := by linarith
      exact_mod_cast h2
    have hdy0 : ((NumberField.discr K : ℤ) : K) • y ≠ 0 :=
      smul_ne_zero (by exact_mod_cast NumberField.discr_ne_zero K) hy0
    obtain ⟨i, hi⟩ := hmin _ hdy hdy0
    have hscale : normSq (Q i *ᵥ embVec (σ i) (((NumberField.discr K : ℤ) : K) • y)) =
        dK ^ 2 * normSq (Q i *ᵥ embVec (σ i) y) := by
      rw [embVec_smul, Matrix.mulVec_smul, map_intCast]
      simp only [normSq, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum, Complex.norm_intCast]
      rw [hdK, sq_abs]
    have huu : u ⬝ᵥ u = majSq σ Q y := by rw [← hu', theta_dot_self, phi_dot_self]
    rw [huu, hμ', div_pow, div_le_iff₀ (by positivity)]
    have hle : normSq (Q i *ᵥ embVec (σ i) y) ≤ majSq σ Q y :=
      Finset.single_le_sum (f := fun i => normSq (Q i *ᵥ embVec (σ i) y))
        (fun j _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    calc laStar ^ 2 ≤ dK ^ 2 * normSq (Q i *ᵥ embVec (σ i) y) := hscale ▸ hi
      _ ≤ dK ^ 2 * majSq σ Q y := mul_le_mul_of_nonneg_left hle (sq_nonneg _)
      _ = majSq σ Q y * dK ^ 2 := mul_comm _ _

  have hRdet : IsUnit ((A⁻¹)ᵀ).det := by
    rw [Matrix.det_transpose]
    exact Matrix.isUnit_nonsing_inv_det A hAu
  have hRinv : ((A⁻¹)ᵀ)⁻¹ᵀ = A := by
    have h1 : ((A⁻¹)ᵀ)⁻¹ = Aᵀ := Matrix.inv_eq_right_inv (by
      rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv A hAu, Matrix.transpose_one])
    rw [h1, Matrix.transpose_transpose]
  have hdual' : ∀ t : Fin N → ℤ, t ≠ 0 → μ' ^ 2 ≤
      (fun i => (t i : ℝ)) ⬝ᵥ (((A⁻¹)ᵀᵀ * (A⁻¹)ᵀ) *ᵥ fun i => (t i : ℝ)) := by
    intro t ht
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    exact hdual t ht
  obtain ⟨c, hcli, hcb⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin.shortDual_holds N ((A⁻¹)ᵀᵀ * (A⁻¹)ᵀ) (A⁻¹)ᵀ μ' hNpos rfl
    hRdet hμ'pos hdual' (N / μ') (by positivity)
  rw [hRinv] at hcb

  set v : Fin N → Fin r → K := fun j => ∑ k, ((c j k : ℤ) : ℚ) • e k with hv
  have hzsm : ∀ (n : ℤ) (x : Fin r → K), x ∈ L → ((n : ℚ) • x) ∈ L := by
    intro n x hx
    rw [Int.cast_smul_eq_zsmul]
    exact L.toAddSubgroup.zsmul_mem hx n
  have hvL : ∀ j, v j ∈ L := fun j => L.sum_mem fun k _ => hzsm _ _ (heL k)
  have hAv : ∀ j, A *ᵥ (fun k => (c j k : ℝ)) = rho eqv (Phi σ Q (v j)) := by
    intro j
    rw [hv, ← hAQ]
    congr 1
  set ℓ : ℝ := 2 * (N : ℝ) / μ' with hℓ
  have hcb' : ∀ j, (A *ᵥ fun k => (c j k : ℝ)) ⬝ᵥ (A *ᵥ fun k => (c j k : ℝ)) ≤ ℓ ^ 2 := by
    intro j
    have h1 := hcb j
    have h2 : ((N : ℝ) / μ' + N / μ') = ℓ := by rw [hℓ]; ring
    rwa [h2] at h1
  have hvb : ∀ j, majSq σ Q (v j) ≤ ℓ ^ 2 := by
    intro j
    rw [← phi_dot_self σ Q eqv, ← hAv j]
    exact hcb' j

  let Cz : Matrix (Fin N) (Fin N) ℤ := Matrix.of c
  have hCz : Cz.det ≠ 0 := by
    intro h0
    obtain ⟨m, hm0, hm⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    apply hm0
    funext j
    refine Fintype.linearIndependent_iff.1 hcli m ?_ j
    funext k
    have h1 := congrFun hm k
    simpa [Matrix.vecMul, dotProduct, Cz, Finset.sum_apply] using h1
  have hCR : (Cz.map (Int.castRingHom ℝ)).det ≠ 0 := by
    rw [show Cz.map (Int.castRingHom ℝ) = (Int.castRingHom ℝ).mapMatrix Cz from rfl, ← RingHom.map_det]
    simpa using hCz
  have hCQ : (Cz.map (Int.castRingHom ℚ)).det ≠ 0 := by
    rw [show Cz.map (Int.castRingHom ℚ) = (Int.castRingHom ℚ).mapMatrix Cz from rfl, ← RingHom.map_det]
    simpa using hCz
  have hvli : LinearIndependent ℚ v := by
    rw [Fintype.linearIndependent_iff]
    intro q hq
    have h1 : ∑ k, (∑ j, q j * (c j k : ℚ)) • e k = 0 := by
      rw [← hq]
      simp only [hv, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    have h2 := Fintype.linearIndependent_iff.1 heli _ h1
    have h3 : q ᵥ* (Cz.map (Int.castRingHom ℚ)) = 0 := by
      funext k
      simpa [Matrix.vecMul, dotProduct, Cz] using h2 k
    exact fun j => congrFun (Matrix.eq_zero_of_vecMul_eq_zero hCQ h3) j
  have hspanQ : Submodule.span ℚ (Set.range v) = ⊤ :=
    hvli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, hfinrank])
  have hspanK : Submodule.span K (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span ℚ (Set.range v) := hspanQ ▸ Submodule.mem_top
    exact Submodule.span_le_restrictScalars ℚ K _ hx
  obtain ⟨vb, hvbS, hvbli⟩ := exists_basis_in (Set.range v) hspanK

  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast Fintype.card_pos
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr0
  set X : ℝ := (f : ℝ) * r with hX
  have hX1 : 1 ≤ X := one_le_mul_of_one_le_of_one_le hf1 hr1
  have hNX : (N : ℝ) = 2 * X := by rw [hN, hdeg, hX]; push_cast; ring
  set Dq : ℝ := dK / laStar with hDq
  have hDqpos : 0 < Dq := div_pos hdpos hla
  have hμval : μ = 4 * X ^ 3 * Dq := by
    show ReciprocityTheory.ChartRestriction.G.FD.d5mu (Fintype.card ι) r |(NumberField.discr K : ℝ)| laStar = _
    simp only [ReciprocityTheory.ChartRestriction.G.FD.d5mu, hX, hDq]
    ring
  have hℓval : ℓ = 4 * X * Dq := by
    rw [hℓ, hNX, hμ', hDq]
    field_simp
    ring
  have hX3 : X ≤ X ^ 3 := by simpa using pow_le_pow_right₀ hX1 (show 1 ≤ 3 by norm_num)
  have hX23 : X ^ 2 ≤ X ^ 3 := pow_le_pow_right₀ hX1 (by norm_num)
  have hℓμ : ℓ ^ 2 ≤ μ ^ 2 := by
    refine pow_le_pow_left₀ (by rw [hℓval]; positivity) ?_ 2
    rw [hℓval, hμval]
    nlinarith
  have hcovμ : ((N : ℝ) * ℓ / 2) ^ 2 ≤ μ ^ 2 := by
    refine pow_le_pow_left₀ (by rw [hℓval, hNX]; positivity) ?_ 2
    rw [hℓval, hμval, hNX]
    nlinarith
  refine ⟨fun w => ?_, vb, fun j => ?_, hvbli, fun j => ?_⟩
  ·
    have hbli : LinearIndependent ℝ (fun j => A *ᵥ (fun k => (c j k : ℝ))) := by
      rw [Fintype.linearIndependent_iff]
      intro a ha
      have h1 : A *ᵥ (a ᵥ* Cz.map (Int.castRingHom ℝ)) = 0 := by
        calc A *ᵥ (a ᵥ* Cz.map (Int.castRingHom ℝ)) = A *ᵥ (∑ i, a i • fun k => (c i k : ℝ)) := by
              congr 1
              funext k
              simp [Matrix.vecMul, dotProduct, Cz, Finset.sum_apply]
          _ = ∑ i, a i • A *ᵥ fun k => (c i k : ℝ) := by
              rw [Matrix.mulVec_sum]
              simp [Matrix.mulVec_smul]
          _ = 0 := ha
      have h2 := Matrix.eq_zero_of_mulVec_eq_zero hAdet h1
      exact fun j => congrFun (Matrix.eq_zero_of_vecMul_eq_zero hCR h2) j
    have hcr := cover_round (N := N) (fun j => A *ᵥ (fun k => (c j k : ℝ))) hbli ℓ hcb' (rho eqv w)
    obtain ⟨n, hn⟩ := hcr
    have hlL : (∑ j, ((n j : ℤ) : ℚ) • v j) ∈ L := Submodule.sum_mem L fun j _ => hzsm (n j) (v j) (hvL j)
    refine ⟨_, hlL, ?_⟩
    have hsumr : ∑ j, (n j : ℝ) • (A *ᵥ (fun k => (c j k : ℝ))) =
        rho eqv (Phi σ Q (∑ j, ((n j : ℤ) : ℚ) • v j)) := by
      rw [Phi_sum, rho_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Phi_qsmul, rho_smul, hAv j]
      simp [Rat.cast_intCast]
    rw [hsumr] at hn
    have heq : ∑ i, normSq (Q i *ᵥ embVec (σ i) (∑ j, ((n j : ℤ) : ℚ) • v j) - w i) =
        (rho eqv w - rho eqv (Phi σ Q (∑ j, ((n j : ℤ) : ℚ) • v j))) ⬝ᵥ
          (rho eqv w - rho eqv (Phi σ Q (∑ j, ((n j : ℤ) : ℚ) • v j))) := by
      rw [← rho_sub, rho_dot_self]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [normSq, Phi, Pi.sub_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← norm_neg, neg_sub]
    rw [heq]
    exact hn.trans hcovμ
  · obtain ⟨j', hj'⟩ := hvbS j
    rw [← hj']
    exact hvL j'
  · obtain ⟨j', hj'⟩ := hvbS j
    rw [← hj']
    exact (hvb j').trans hℓμ
end Formalism.L2.Pj.FundamentalDomainD5
