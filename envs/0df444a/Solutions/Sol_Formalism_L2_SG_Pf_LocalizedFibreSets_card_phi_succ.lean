-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LocalizedFibreSets.card_phi_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:21:41.045049+00:00
-- url     : https://prove2.me/submissions/8b197dd9-e8e2-4f19-9053-b7dec0616a80

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscOnto
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CardPhiSucc
import Theorems.Thm_Formalism_L2_SG_Pf_LocalizedFibreSets_diagQ_herm
import Theorems.Thm_Formalism_L2_SG_Pf_LocalizedFibreSets_phiQ_herm
import Theorems.Thm_Formalism_L2_SG_Pf_LocalizedFibreSets_map_phiQ
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_finite_quot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_card_hermSub_sq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_range_trH
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_finite_quot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormResidues_finite_quot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_finite_quot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mk_mem_ker_piQ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_piQ_star
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_piQ_surjective
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_reductionMapsOfForms_card_hermSub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_reductionMapsOfForms_exists_unit_quot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_zero
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_zero



set_option autoImplicit false
open NumberField Module Matrix
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LocalizedFibreSets
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HermitianSublattices Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
  Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}
namespace Formalism.L2.SG.Pf.LocalizedFibreSets
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (a : Fin m → 𝓞 F) {k : ℕ} (hk : 1 ≤ k) (T : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)))
    (hT : Tᴴ = T) (hT0 : ∀ i j, T i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)))) :
    Nat.card {Y // phiQ K 𝔭 (k + 1) a Y = T} =
      Ideal.absNorm 𝔭 ^ (m * m) * Nat.card {Y // phiQ K 𝔭 k a Y = T.map (piQ K 𝔭 k)} := by
  classical
  haveI := finite_quot (K := K) h𝔭 (k + 1)
  haveI := finite_quot (K := K) h𝔭 k
  haveI : Finite (Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ (k + 1))) := inferInstanceAs (Finite (Fin m → Fin m → (𝓞 K ⧸ extP K 𝔭 ^ (k + 1))))
  haveI : Finite (Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) :=
    inferInstanceAs (Finite (Fin m → Fin m → (𝓞 K ⧸ extP K 𝔭 ^ k)))

  have hJJ : ∀ x ∈ (RingHom.ker (piQ K 𝔭 k)), ∀ y ∈ (RingHom.ker (piQ K 𝔭 k)), x * y = 0 := by
    intro x hx y hy
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [mk_mem_ker_piQ] at hx hy
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    have huv : u * v ∈ extP K 𝔭 ^ (k + k) := by rw [pow_add]; exact Ideal.mul_mem_mul hx hy
    exact Ideal.pow_le_pow_right (by omega) huv
  have hPJ : ∀ x ∈ ((extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)))), ∀ y ∈ (RingHom.ker (piQ K 𝔭 k)), x * y = 0 := by
    intro x hx y hy
    obtain ⟨u, hu, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hx
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [mk_mem_ker_piQ] at hy
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, pow_succ']
    exact Ideal.mul_mem_mul hu hy
  have hJP : ∀ x ∈ (RingHom.ker (piQ K 𝔭 k)), x ∈ ((extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)))) := by
    intro x hx
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [mk_mem_ker_piQ] at hx
    exact Ideal.mem_map_of_mem _ (Ideal.pow_le_self (by omega) hx)
  have hJs : ∀ x ∈ (RingHom.ker (piQ K 𝔭 k)), star x ∈ (RingHom.ker (piQ K 𝔭 k)) := by
    intro x hx
    rw [RingHom.mem_ker] at hx ⊢
    rw [piQ_star, hx, star_zero]
  obtain ⟨θ, e, he⟩ := exists_unit_quot hK h𝔭 (k + 1)
  have hmem : ∀ (C E : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ (k + 1))), E ∈ Formalism.HermitianLattices.Ext.L3.HermitianSublattices.entSub (Fin m) (Fin m) (RingHom.ker (piQ K 𝔭 k)) → C * E ∈ Formalism.HermitianLattices.Ext.L3.HermitianSublattices.entSub (Fin m) (Fin m) (RingHom.ker (piQ K 𝔭 k)) := by
    intro C E hE i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ (fun l _ => Ideal.mul_mem_left _ _ (hE l j))

  have hfib : ∀ (A B : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ (k + 1))), (∀ G ∈ Formalism.HermitianLattices.Ext.L3.HermitianSublattices.entSub (Fin m) (Fin m) (RingHom.ker (piQ K 𝔭 k)), A * (B * G) = G) →
      ∀ S ∈ Formalism.HermitianLattices.Ext.L3.HermitianSublattices.hermSub (Fin m) (RingHom.ker (piQ K 𝔭 k)), Nat.card {E : Formalism.HermitianLattices.Ext.L3.HermitianSublattices.entSub (Fin m) (Fin m) (RingHom.ker (piQ K 𝔭 k)) // A * E.1 + (A * E.1)ᴴ = S} =
        Ideal.absNorm 𝔭 ^ (m * m) := by
    intro A B hAB S hS
    let L : Formalism.HermitianLattices.Ext.L3.HermitianSublattices.entSub (Fin m) (Fin m) (RingHom.ker (piQ K 𝔭 k)) →+ Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) :=
      (Formalism.HermitianLattices.Ext.L3.HermitianSublattices.trH (Fin m) (RingHom.ker (piQ K 𝔭 k))).comp
        (AddMonoidHom.mk' (fun E => ⟨A * E.1, hmem A E.1 E.2⟩)
          (fun E F => Subtype.ext (by simp [Matrix.mul_add])))
    have hL : ∀ E, L E = A * E.1 + (A * E.1)ᴴ := fun E => rfl
    have hrange : L.range = Formalism.HermitianLattices.Ext.L3.HermitianSublattices.hermSub (Fin m) (RingHom.ker (piQ K 𝔭 k)) := by
      apply le_antisymm
      · rintro _ ⟨E, rfl⟩
        rw [← Formalism.HermitianLattices.Ext.L3.HermitianSublattices.range_trH hJs he]
        exact ⟨⟨A * E.1, hmem _ _ E.2⟩, rfl⟩
      · intro S' hS'
        rw [← Formalism.HermitianLattices.Ext.L3.HermitianSublattices.range_trH hJs he] at hS'
        obtain ⟨G, rfl⟩ := hS'
        refine ⟨⟨B * G.1, hmem _ _ G.2⟩, ?_⟩
        rw [hL]
        show A * (B * G.1) + (A * (B * G.1))ᴴ = G.1 + G.1ᴴ
        rw [hAB G.1 G.2]
    have hcardE : Nat.card (Formalism.HermitianLattices.Ext.L3.HermitianSublattices.entSub (Fin m) (Fin m) (RingHom.ker (piQ K 𝔭 k))) = Nat.card L.ker * Nat.card (Formalism.HermitianLattices.Ext.L3.HermitianSublattices.hermSub (Fin m) (RingHom.ker (piQ K 𝔭 k))) := by
      rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup L.ker,
        Nat.card_congr (QuotientAddGroup.quotientKerEquivRange L).toEquiv, hrange, mul_comm]
    have hsq := Formalism.HermitianLattices.Ext.L3.HermitianSublattices.card_hermSub_sq (r := Fin m) hJs he
    have hh := Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms.card_hermSub (r := Fin m) hK h𝔭 k
    rw [Fintype.card_fin] at hh
    have hpos : 0 < Nat.card (Formalism.HermitianLattices.Ext.L3.HermitianSublattices.hermSub (Fin m) (RingHom.ker (piQ K 𝔭 k))) := Nat.card_pos
    have hker : Nat.card L.ker = Nat.card (Formalism.HermitianLattices.Ext.L3.HermitianSublattices.hermSub (Fin m) (RingHom.ker (piQ K 𝔭 k))) := by
      rw [← hsq, pow_two] at hcardE
      exact (Nat.eq_of_mul_eq_mul_right hpos hcardE).symm
    have hSr : S ∈ L.range := by rw [hrange]; exact hS
    obtain ⟨E0, hE0⟩ := hSr
    rw [← hh, ← hker]
    exact Nat.card_congr
      { toFun := fun E => ⟨E.1 - E0, by
          rw [AddMonoidHom.mem_ker, map_sub, hE0, hL, E.2, sub_self]⟩
        invFun := fun K0 => ⟨K0.1 + E0, by
          rw [← hL, map_add, AddMonoidHom.mem_ker.mp K0.2, hE0, zero_add]⟩
        left_inv := fun E => Subtype.ext (sub_add_cancel _ _)
        right_inv := fun K0 => Subtype.ext (add_sub_cancel_right _ _) }

  let f : {Y // phiQ K 𝔭 (k + 1) a Y = T} → {Y // phiQ K 𝔭 k a Y = T.map (piQ K 𝔭 k)} :=
    fun Y => ⟨Y.1.map (piQ K 𝔭 k), by rw [← map_phiQ, Y.2]⟩
  have hfiber : ∀ y, Nat.card {x // f x = y} = Ideal.absNorm 𝔭 ^ (m * m) := by
    rintro ⟨Y', hY'⟩
    obtain ⟨Y0, hY0⟩ : ∃ Y0 : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)), Y0.map (piQ K 𝔭 k) = Y' :=
      ⟨fun i j => (piQ_surjective (K := K) 𝔭 k (Y' i j)).choose,
        by ext i j; exact (piQ_surjective (K := K) 𝔭 k (Y' i j)).choose_spec⟩
    obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)), A = 1 + Y0ᴴ * diagQ K 𝔭 (k + 1) a := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)), B = 1 + Y0 * diagQ K 𝔭 (k + 1) a := ⟨_, rfl⟩
    have hS : T - phiQ K 𝔭 (k + 1) a Y0 ∈ Formalism.HermitianLattices.Ext.L3.HermitianSublattices.hermSub (Fin m) (RingHom.ker (piQ K 𝔭 k)) := by
      refine ⟨?_, ?_⟩
      · rw [Matrix.conjTranspose_sub, hT, phiQ_herm]
      · intro i j
        rw [RingHom.mem_ker, Matrix.sub_apply, map_sub]
        have h1 := congrFun (congrFun (map_phiQ 𝔭 k a Y0) i) j
        rw [Matrix.map_apply] at h1
        rw [h1, hY0, hY', Matrix.map_apply, sub_self]
    have hPhi0 : ∀ i j, phiQ K 𝔭 (k + 1) a Y0 i j ∈ ((extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)))) := by
      intro i j
      have e1 : phiQ K 𝔭 (k + 1) a Y0 i j = T i j - (T - phiQ K 𝔭 (k + 1) a Y0) i j := by
        rw [Matrix.sub_apply]; ring
      rw [e1]
      exact Ideal.sub_mem _ (hT0 i j) (hJP _ (hS.2 i j))
    have hAB : A * B = 1 + phiQ K 𝔭 (k + 1) a Y0 * diagQ K 𝔭 (k + 1) a := by
      rw [hA, hB]; unfold phiQ; noncomm_ring
    have hABG : ∀ G ∈ Formalism.HermitianLattices.Ext.L3.HermitianSublattices.entSub (Fin m) (Fin m) (RingHom.ker (piQ K 𝔭 k)), A * (B * G) = G := by
      intro G hG
      have h0 : phiQ K 𝔭 (k + 1) a Y0 * diagQ K 𝔭 (k + 1) a * G = 0 := by
        ext i j
        rw [Matrix.mul_apply, Matrix.zero_apply]
        refine Finset.sum_eq_zero (fun l _ => hPJ _ ?_ _ (hG l j))
        rw [Matrix.mul_apply]
        exact Ideal.sum_mem _ (fun l' _ => Ideal.mul_mem_right _ _ (hPhi0 i l'))
      rw [← Matrix.mul_assoc, hAB, Matrix.add_mul, Matrix.one_mul, h0, add_zero]
    have hEE : ∀ E ∈ Formalism.HermitianLattices.Ext.L3.HermitianSublattices.entSub (Fin m) (Fin m) (RingHom.ker (piQ K 𝔭 k)), Eᴴ * diagQ K 𝔭 (k + 1) a * E = 0 := by
      intro E hE
      ext i j
      rw [Matrix.mul_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero (fun l _ => hJJ _ ?_ _ (hE l j))
      rw [Matrix.mul_apply]
      refine Ideal.sum_mem _ (fun l' _ => Ideal.mul_mem_right _ _ ?_)
      rw [Matrix.conjTranspose_apply]
      exact hJs _ (hE l' i)
    have hDh : (diagQ K 𝔭 (k + 1) a)ᴴ = diagQ K 𝔭 (k + 1) a := diagQ_herm 𝔭 (k + 1) a
    have hexp : ∀ E ∈ Formalism.HermitianLattices.Ext.L3.HermitianSublattices.entSub (Fin m) (Fin m) (RingHom.ker (piQ K 𝔭 k)), phiQ K 𝔭 (k + 1) a (Y0 + E) =
        phiQ K 𝔭 (k + 1) a Y0 + (A * E + (A * E)ᴴ) := by
      intro E hE
      have h1 : (A * E)ᴴ = Eᴴ * (1 + diagQ K 𝔭 (k + 1) a * Y0) := by
        rw [Matrix.conjTranspose_mul, hA, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
          Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hDh]
      rw [h1, hA]
      unfold phiQ
      rw [Matrix.conjTranspose_add]
      calc _ = Y0 + Y0ᴴ + Y0ᴴ * diagQ K 𝔭 (k + 1) a * Y0 +
            ((1 + Y0ᴴ * diagQ K 𝔭 (k + 1) a) * E + Eᴴ * (1 + diagQ K 𝔭 (k + 1) a * Y0)) + Eᴴ * diagQ K 𝔭 (k + 1) a * E := by noncomm_ring
        _ = _ := by rw [hEE E hE, add_zero]
    have hker0 : ∀ E ∈ Formalism.HermitianLattices.Ext.L3.HermitianSublattices.entSub (Fin m) (Fin m) (RingHom.ker (piQ K 𝔭 k)), E.map (piQ K 𝔭 k) = 0 := by
      intro E hE
      ext i j
      exact hE i j
    rw [← hfib A B hABG _ hS]
    exact Nat.card_congr
      { toFun := fun x => ⟨⟨x.1.1 - Y0, by
            intro i j
            have hx := congrArg Subtype.val x.2
            have hx' := congrFun (congrFun hx i) j
            rw [RingHom.mem_ker, Matrix.sub_apply, map_sub]
            have hy := congrFun (congrFun hY0 i) j
            simp only [f, Matrix.map_apply] at hx' hy
            rw [hx', hy, sub_self]⟩, by
            have h2 := hexp (x.1.1 - Y0) (by
              intro i j
              have hx := congrArg Subtype.val x.2
              have hx' := congrFun (congrFun hx i) j
              rw [RingHom.mem_ker, Matrix.sub_apply, map_sub]
              have hy := congrFun (congrFun hY0 i) j
              simp only [f, Matrix.map_apply] at hx' hy
              rw [hx', hy, sub_self])
            rw [add_sub_cancel, x.1.2] at h2
            show A * (x.1.1 - Y0) + (A * (x.1.1 - Y0))ᴴ = T - phiQ K 𝔭 (k + 1) a Y0
            exact eq_sub_of_add_eq' h2.symm⟩
        invFun := fun E => ⟨⟨Y0 + E.1.1, by rw [hexp E.1.1 E.1.2, E.2, add_sub_cancel]⟩,
          Subtype.ext (by
            show (Y0 + E.1.1).map (piQ K 𝔭 k) = Y'
            rw [Matrix.map_add _ (map_add _), hY0, hker0 E.1.1 E.1.2, add_zero])⟩
        left_inv := fun x => Subtype.ext (Subtype.ext (add_sub_cancel _ _))
        right_inv := fun E => Subtype.ext (Subtype.ext (add_sub_cancel_left _ _)) }
  haveI : Fintype {Y // phiQ K 𝔭 k a Y = T.map (piQ K 𝔭 k)} := Fintype.ofFinite _
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma,
    Finset.sum_congr rfl (fun y _ => hfiber y), Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, smul_eq_mul, mul_comm]
end Formalism.L2.SG.Pf.LocalizedFibreSets
