-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.exists_bijective_cartierModule_XS_awayHom_of_etaPiece_bijective_of_isAlgClosed_of_lieZero_le_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/c263f2f8-a418-5bd6-99df-6dc85ec4de34

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_PeriodMapSpec
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_CriticalIndexChart
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_linearMap_bijOn_gradedPiece_apply_eq_of_bijective_invariants_of_isCritical_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_FormalODModule_apply_mkQ_eq_mkQ_and_mem_vRange_iff_of_apply_eq_nMk_of_isCritical_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_FormalODModule_endAct_actEnd_comp_eq_of_forall_teichmuller_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCanonicalLMap_apply_eq_nMk_of_charP
import Theorems.Thm_CerednikDrinfeld_FormalODModule_mem_etaPiece_iff_of_isCanonicalLMap_apply_eq_nMk_of_charP
import Theorems.Thm_CerednikDrinfeld_FormalODModule_eq_zero_of_endAct_varpiEnd_eq_zero_of_isReduced
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical
import Theorems.Thm_CerednikDrinfeld_FormalODModule_IsSpecial_map
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_bijective_cartierModule_XS_awayHom_of_etaPiece_bijective_of_isAlgClosed_of_lieZero_le_ker
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

noncomputable section

namespace CritExtendBlocks

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.FormalODModule

theorem vLift (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [IsAlgClosed K] (j : Zp2 p →+* K)
    (X X' : FormalODModule p K)
    (hVinj' : Function.Injective (verschiebungInt : CartierModule p X'.F → CartierModule p X'.F))
    (Θ : CartierModule p X.F →ₗ[WittVector p K] CartierModule p X'.F)
    (n : ℕ)
    (hex : ∀ y ∈ X.gradedPiece j n, ∃ y' : CartierModule p X'.F, verschiebungInt y' = Θ (verschiebungInt y)) :
    ∃ Θ₁ : X.gradedSubmodule j n →ₗ[WittVector p K] CartierModule p X'.F,
      ∀ y : X.gradedSubmodule j n, verschiebungInt (Θ₁ y) = Θ (verschiebungInt (y : CartierModule p X.F)) := by
  classical
  haveI : PerfectRing K p := inferInstance
  have hσ : Function.Surjective (WittVector.frobenius : WittVector p K →+* WittVector p K) :=
    (WittVector.frobeniusEquiv p K).surjective
  let g : X.gradedSubmodule j n → CartierModule p X'.F := fun y => Classical.choose (hex y.1 y.2)
  have hg : ∀ y : X.gradedSubmodule j n, verschiebungInt (g y) = Θ (verschiebungInt (y : CartierModule p X.F)) :=
    fun y => Classical.choose_spec (hex y.1 y.2)
  refine ⟨{ toFun := g, map_add' := ?_, map_smul' := ?_ }, fun y => hg y⟩
  · intro a b
    apply hVinj'
    rw [hg, map_add, Submodule.coe_add, map_add, map_add, hg, hg]
  · intro w a
    apply hVinj'
    obtain ⟨u, rfl⟩ := hσ w
    show verschiebungInt (g (WittVector.frobenius u • a)) = verschiebungInt (WittVector.frobenius u • g a)
    rw [hg, Submodule.coe_smul, ← smul_verschiebungInt, ← smul_verschiebungInt, map_smul, hg]

end CritExtendBlocks

namespace CritExtendBlocks

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.FormalODModule

theorem teich_comm (p : ℕ) [Fact p.Prime] (K : Type) [CommRing K] (j : Zp2 p →+* K)
    (X X' : FormalODModule p K) (n : ℕ)
    (hcP : IsCompl (X.gradedSubmodule j n) (X.gradedSubmodule j (n + 1)))
    (θ : CartierModule p X.F →ₗ[WittVector p K] CartierModule p X'.F)
    (h0 : ∀ x ∈ X.gradedPiece j n, θ x ∈ X'.gradedPiece j n)
    (h1 : ∀ y ∈ X.gradedPiece j (n + 1), θ y ∈ X'.gradedPiece j (n + 1)) :
    ∀ (c : GaloisField p 2) (f : CartierModule p X.F),
      θ (endAct (X.actEnd (WittVector.teichmuller p c)) f) = endAct (X'.actEnd (WittVector.teichmuller p c)) (θ f) := by
  intro c f
  classical
  obtain ⟨f₀, hf₀, f₁, hf₁, rfl⟩ := Submodule.mem_sup.1
    ((hcP.codisjoint.eq_top.symm ▸ Submodule.mem_top : f ∈ X.gradedSubmodule j n ⊔ X.gradedSubmodule j (n + 1)))
  have hf₀' : f₀ ∈ X.gradedPiece j n := hf₀
  have hf₁' : f₁ ∈ X.gradedPiece j (n + 1) := hf₁
  rw [map_add, map_add, map_add, map_add,
    (mem_gradedPiece_iff X j n f₀).1 hf₀' c, (mem_gradedPiece_iff X j (n + 1) f₁).1 hf₁' c,
    (mem_gradedPiece_iff X' j n _).1 (h0 f₀ hf₀') c, (mem_gradedPiece_iff X' j (n + 1) _).1 (h1 f₁ hf₁') c,
    ← teichmuller_smul, ← teichmuller_smul, ← teichmuller_smul, ← teichmuller_smul, map_smul, map_smul]

end CritExtendBlocks

end

noncomputable section

namespace CritExtendAsm

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.GradedCartierModuleData CerednikDrinfeld.FormalODModule

theorem nMk_fst_injective {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}
    (E : GradedCartierModuleData p B j) (htors : ∀ m : E.M, E.varpi m = 0 → m = 0)
    (m m' : E.M) (h : E.nMk (m, 0) = E.nMk (m', 0)) : m = m' := by
  rw [nMk_apply, nMk_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h
  obtain ⟨x, hx⟩ : ∃ x, E.nRelMap x = (m, E.toSigma 0) - (m', E.toSigma 0) := LinearMap.mem_range.mp h
  rw [nRelMap_apply, Prod.mk_sub_mk, Prod.mk.injEq] at hx
  obtain ⟨h1, h2⟩ := hx
  have hneg : -E.varpi (E.ofSigma x) = 0 := by
    have h3 : E.toSigma (-E.varpi (E.ofSigma x)) = 0 := by rw [h2, sub_self]
    exact h3
  have hx0 : E.ofSigma x = 0 := htors _ (neg_eq_zero.mp hneg)
  rw [hx0, map_zero] at h1
  exact (sub_eq_zero.mp h1.symm)

theorem hasHeight_map_field {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] (X : FormalODModule p B)
    (hX4 : X.HasHeight 4) {K : Type} [Field K] (g : B →+* K) : (X.map g).HasHeight 4 := by
  obtain ⟨-, -, hfib⟩ := hX4
  have hK : Module.finrank K (FormalODModule.KerAlgebra ((X.act (p : Zp2 p)).map g)) = p ^ 4 := hfib K g
  show FormalODModule.HasKernelOfDegree ((X.map g).act (p : Zp2 p)) (p ^ 4)
  rw [FormalODModule.map_act]
  refine ⟨?_, ?_, fun κ _ f => ?_⟩
  · exact Module.finite_of_finrank_pos (by rw [hK]; exact pow_pos (Nat.Prime.pos Fact.out) 4)
  · exact Module.Projective.of_free
  · rw [CerednikDrinfeld.SpecialFormal.Series.map_map]; exact hfib κ (f.comp g)

theorem isAlgClosed_of_ringEquiv {F F' : Type} [Field F] [Field F'] [IsAlgClosed F] (e : F ≃+* F') :
    IsAlgClosed F' := by
  refine IsAlgClosed.of_exists_root F' fun q _ hqi => ?_
  set q' : Polynomial F := q.map e.symm.toRingHom with hq'def
  have hq' : q'.degree ≠ 0 := by
    rw [hq'def, Polynomial.degree_map_eq_of_injective e.symm.injective]
    exact (Polynomial.degree_pos_of_irreducible hqi).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root q' hq'
  refine ⟨e x, ?_⟩
  have hqq : q = q'.map e.toRingHom := by
    rw [hq'def, Polynomial.map_map, RingEquiv.toRingHom_comp_symm_toRingHom, Polynomial.map_id]
  rw [hqq, Polynomial.eval_map]
  show Polynomial.eval₂ e.toRingHom (e.toRingHom x) q' = 0
  rw [Polynomial.eval₂_at_apply, hx.eq_zero, map_zero]

end CritExtendAsm

end

set_option maxHeartbeats 6400000 in
open CritExtendAsm MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.GradedCartierModuleData CerednikDrinfeld.FormalODModule in

theorem CritExtendAsm.assemble
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [IsAlgClosed K] (j : Zp2 p →+* K)
    (X X' : FormalODModule p K) (hX : X.IsSpecial j) (hX4 : X.HasHeight 4)
    (hX' : X'.IsSpecial j) (hX'4 : X'.HasHeight 4)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1)) (hc' : IsCompl (X'.gradedPiece j 0) (X'.gradedPiece j 1))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod) (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (L' : (X'.toGradedCartierModuleData j hc').M →+ (X'.toGradedCartierModuleData j hc').NMod) (hL' : (X'.toGradedCartierModuleData j hc').IsCanonicalLMap L')
    (i : Fin 2)
    (hi : ∀ m ∈ X.gradedPiece j (i : ℕ), ∃ y : CartierModule p X.F, verschiebungInt y = endAct X.varpiEnd m)
    (hi' : ∀ m ∈ X'.gradedPiece j (i : ℕ), ∃ y : CartierModule p X'.F, verschiebungInt y = endAct X'.varpiEnd m)
    (θη : ((X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i) →+ ((X'.toGradedCartierModuleData j hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i))
    (τ : (X.toGradedCartierModuleData j hc).LieQuot →ₗ[WittVector p K] (X'.toGradedCartierModuleData j hc').LieQuot)
    (hθη : Function.Bijective θη) (hτ : Function.Injective τ)
    (hcompat : ∀ (m : (X.toGradedCartierModuleData j hc).M) (m' : (X'.toGradedCartierModuleData j hc').M) (hm : (X.toGradedCartierModuleData j hc).nMk (m, 0) ∈ ((X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i)),
      ((θη ⟨(X.toGradedCartierModuleData j hc).nMk (m, 0), hm⟩ : ((X'.toGradedCartierModuleData j hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i)) : (X'.toGradedCartierModuleData j hc').NMod) = (X'.toGradedCartierModuleData j hc').nMk (m', 0) →
        τ ((X.toGradedCartierModuleData j hc).vRange.mkQ m) = (X'.toGradedCartierModuleData j hc').vRange.mkQ m') :
    ∃ θ : CartierModule p X.F →+ CartierModule p X'.F,
      Function.Bijective θ ∧
      (∀ f, θ (frobenius f) = frobenius (θ f)) ∧
      (∀ f, θ (verschiebungInt f) = verschiebungInt (θ f)) ∧
      (∀ (w : WittVector p K) f, θ (w • f) = w • θ f) ∧
      (∀ (a : Zp2 p) f, θ (endAct (X.actEnd a) f) = endAct (X'.actEnd a) (θ f)) ∧
      (∀ f, θ (endAct X.varpiEnd f) = endAct X'.varpiEnd (θ f)) ∧
      (∀ (m : (X.toGradedCartierModuleData j hc).M) (hm : (X.toGradedCartierModuleData j hc).nMk (m, 0) ∈ ((X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i)),
        ((θη ⟨(X.toGradedCartierModuleData j hc).nMk (m, 0), hm⟩ : ((X'.toGradedCartierModuleData j hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i)) : (X'.toGradedCartierModuleData j hc').NMod) = (X'.toGradedCartierModuleData j hc').nMk (θ m, 0)) := by
  classical

  have hV : ∀ f : CartierModule p X.F, verschiebungInt f = verschiebung f := fun f => verschiebungInt_apply_eq_verschiebung f
  have hV' : ∀ f : CartierModule p X'.F, verschiebungInt f = verschiebung f := fun f => verschiebungInt_apply_eq_verschiebung f
  have htors : ∀ m : CartierModule p X.F, endAct X.varpiEnd m = 0 → m = 0 :=
    CerednikDrinfeld.FormalODModule.eq_zero_of_endAct_varpiEnd_eq_zero_of_isReduced p j X hX hX4
  have htors' : ∀ m : CartierModule p X'.F, endAct X'.varpiEnd m = 0 → m = 0 :=
    CerednikDrinfeld.FormalODModule.eq_zero_of_endAct_varpiEnd_eq_zero_of_isReduced p j X' hX' hX'4
  have hinj1 : ∀ m m' : CartierModule p X.F, (X.toGradedCartierModuleData j hc).nMk (m, 0) = (X.toGradedCartierModuleData j hc).nMk (m', 0) → m = m' :=
    nMk_fst_injective (X.toGradedCartierModuleData j hc) htors
  have hinj1' : ∀ m m' : CartierModule p X'.F, (X'.toGradedCartierModuleData j hc').nMk (m, 0) = (X'.toGradedCartierModuleData j hc').nMk (m', 0) → m = m' :=
    nMk_fst_injective (X'.toGradedCartierModuleData j hc') htors'

  have hLi : ∀ x y : CartierModule p X.F, x ∈ X.gradedPiece j (i : ℕ) →
      verschiebungInt y = endAct X.varpiEnd x → L x = (X.toGradedCartierModuleData j hc).nMk (y, 0) := fun x y hx hy =>
    CerednikDrinfeld.FormalODModule.isCanonicalLMap_apply_eq_nMk_of_charP p j X hc L hL (i : ℕ) hi x y hx hy
  have hLi' : ∀ x y : CartierModule p X'.F, x ∈ X'.gradedPiece j (i : ℕ) →
      verschiebungInt y = endAct X'.varpiEnd x → L' x = (X'.toGradedCartierModuleData j hc').nMk (y, 0) := fun x y hx hy =>
    CerednikDrinfeld.FormalODModule.isCanonicalLMap_apply_eq_nMk_of_charP p j X' hc' L' hL' (i : ℕ) hi' x y hx hy
  obtain ⟨hmem, -⟩ := CerednikDrinfeld.FormalODModule.mem_etaPiece_iff_of_isCanonicalLMap_apply_eq_nMk_of_charP
    p j X hc L hL htors i hi hLi
  obtain ⟨hmem', -⟩ := CerednikDrinfeld.FormalODModule.mem_etaPiece_iff_of_isCanonicalLMap_apply_eq_nMk_of_charP
    p j X' hc' L' hL' htors' i hi' hLi'

  have hetaInv : ∀ m : CartierModule p X.F, (X.toGradedCartierModuleData j hc).nMk (m, 0) ∈ ((X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i) ↔ m ∈ (CritChart.invariants X j (i : ℕ)) := by
    intro m
    constructor
    · intro h
      obtain ⟨m₁, hm₁, hPV, heq⟩ := (hmem _).1 h
      rw [hinj1 _ _ heq]
      exact ⟨hm₁, by rw [← hV]; exact hPV⟩
    · intro h
      exact (hmem _).2 ⟨m, h.1, by rw [hV]; exact h.2, rfl⟩
  have hetaInv' : ∀ m : CartierModule p X'.F, (X'.toGradedCartierModuleData j hc').nMk (m, 0) ∈ ((X'.toGradedCartierModuleData j hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i) ↔ m ∈ (CritChart.invariants X' j (i : ℕ)) := by
    intro m
    constructor
    · intro h
      obtain ⟨m₁, hm₁, hPV, heq⟩ := (hmem' _).1 h
      rw [hinj1' _ _ heq]
      exact ⟨hm₁, by rw [← hV']; exact hPV⟩
    · intro h
      exact (hmem' _).2 ⟨m, h.1, by rw [hV']; exact h.2, rfl⟩

  have hex0 : ∀ m : (CritChart.invariants X j (i : ℕ)), ∃ m' : CartierModule p X'.F, m' ∈ (CritChart.invariants X' j (i : ℕ)) ∧
      ((θη ⟨(X.toGradedCartierModuleData j hc).nMk ((m : CartierModule p X.F), 0), (hetaInv _).2 m.2⟩ : ((X'.toGradedCartierModuleData j hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i)) : (X'.toGradedCartierModuleData j hc').NMod) = (X'.toGradedCartierModuleData j hc').nMk (m', 0) := by
    intro m
    obtain ⟨m', hm', hPV', heq⟩ := (hmem' _).1 (θη ⟨(X.toGradedCartierModuleData j hc).nMk ((m : CartierModule p X.F), 0), (hetaInv _).2 m.2⟩).2
    exact ⟨m', ⟨hm', by rw [← hV']; exact hPV'⟩, heq⟩
  choose θ₀f hθ₀f_inv hθ₀f_eq using hex0
  let θ₀ : (CritChart.invariants X j (i : ℕ)) →+ (CritChart.invariants X' j (i : ℕ)) :=
    { toFun := fun m => ⟨θ₀f m, hθ₀f_inv m⟩
      map_zero' := by
        apply Subtype.ext
        show θ₀f 0 = 0
        apply hinj1'
        rw [← hθ₀f_eq 0]
        have : (⟨(X.toGradedCartierModuleData j hc).nMk (((0 : (CritChart.invariants X j (i : ℕ))) : CartierModule p X.F), 0), (hetaInv _).2 (0 : (CritChart.invariants X j (i : ℕ))).2⟩ : ((X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i)) = 0 := by
          apply Subtype.ext
          show (X.toGradedCartierModuleData j hc).nMk (((0 : (CritChart.invariants X j (i : ℕ))) : CartierModule p X.F), 0) = 0
          rw [AddSubgroup.coe_zero]
          exact map_zero _
        rw [this, map_zero, AddSubgroup.coe_zero]
        exact (map_zero _).symm
      map_add' := fun a b => by
        apply Subtype.ext
        show θ₀f (a + b) = θ₀f a + θ₀f b
        apply hinj1'
        rw [← hθ₀f_eq (a + b)]
        have : (⟨(X.toGradedCartierModuleData j hc).nMk (((a + b : (CritChart.invariants X j (i : ℕ))) : CartierModule p X.F), 0), (hetaInv _).2 (a + b : (CritChart.invariants X j (i : ℕ))).2⟩ : ((X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i)) =
            ⟨(X.toGradedCartierModuleData j hc).nMk ((a : CartierModule p X.F), 0), (hetaInv _).2 a.2⟩ + ⟨(X.toGradedCartierModuleData j hc).nMk ((b : CartierModule p X.F), 0), (hetaInv _).2 b.2⟩ := by
          apply Subtype.ext
          show (X.toGradedCartierModuleData j hc).nMk (((a + b : (CritChart.invariants X j (i : ℕ))) : CartierModule p X.F), 0) = (X.toGradedCartierModuleData j hc).nMk ((a : CartierModule p X.F), 0) + (X.toGradedCartierModuleData j hc).nMk ((b : CartierModule p X.F), 0)
          rw [AddSubgroup.coe_add, ← map_add (X.toGradedCartierModuleData j hc).nMk, Prod.mk_add_mk, add_zero]
          rfl
        rw [this, map_add, AddSubgroup.coe_add, hθ₀f_eq a, hθ₀f_eq b, ← map_add (X'.toGradedCartierModuleData j hc').nMk, Prod.mk_add_mk, add_zero]
        rfl }
  have hθ₀_apply : ∀ m : (CritChart.invariants X j (i : ℕ)), ((θ₀ m : (CritChart.invariants X' j (i : ℕ))) : CartierModule p X'.F) = θ₀f m := fun m => rfl
  have hθ₀_bij : Function.Bijective θ₀ := by
    constructor
    · intro a b hab
      have h1 : θ₀f a = θ₀f b := by
        have := congrArg (fun u : (CritChart.invariants X' j (i : ℕ)) => (u : CartierModule p X'.F)) hab
        exact this
      have h2 := (hθ₀f_eq a).trans ((congrArg (fun u => (X'.toGradedCartierModuleData j hc').nMk (u, 0)) h1).trans (hθ₀f_eq b).symm)
      have h3 := hθη.1 (Subtype.ext h2)
      exact Subtype.ext (hinj1 _ _ (congrArg Subtype.val h3))
    · intro m'
      obtain ⟨z, hz⟩ := hθη.2 ⟨(X'.toGradedCartierModuleData j hc').nMk ((m' : CartierModule p X'.F), 0), (hetaInv' _).2 m'.2⟩
      obtain ⟨m, hm, hPV, hzeq⟩ := (hmem _).1 z.2
      have hminv : m ∈ (CritChart.invariants X j (i : ℕ)) := ⟨hm, by rw [← hV]; exact hPV⟩
      refine ⟨⟨m, hminv⟩, ?_⟩
      apply Subtype.ext
      show θ₀f ⟨m, hminv⟩ = m'
      apply hinj1'
      rw [← hθ₀f_eq]
      have hz' : (⟨(X.toGradedCartierModuleData j hc).nMk (m, 0), (hetaInv _).2 hminv⟩ : ((X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i)) = z := Subtype.ext hzeq.symm
      rw [hz', hz]

  have hicrit : CritChart.IsCritical X j (i : ℕ) := fun m hm => by
    obtain ⟨y, hy⟩ := hi m hm; exact ⟨y, by rw [← hV]; exact hy⟩
  have hicrit' : CritChart.IsCritical X' j (i : ℕ) := fun m hm => by
    obtain ⟨y, hy⟩ := hi' m hm; exact ⟨y, by rw [← hV']; exact hy⟩
  obtain ⟨Θ, hΘbij, hΘinv⟩ :=
    CerednikDrinfeld.FormalODModule.exists_linearMap_bijOn_gradedPiece_apply_eq_of_bijective_invariants_of_isCritical_of_isAlgClosed
      p K j X X' hX hX4 hX' hX'4 (i : ℕ) hicrit hicrit' θ₀ hθ₀_bij

  have hΘ : ∀ (m : CartierModule p X.F) (hm : (X.toGradedCartierModuleData j hc).nMk (m, 0) ∈ ((X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i)),
      ((θη ⟨(X.toGradedCartierModuleData j hc).nMk (m, 0), hm⟩ : ((X'.toGradedCartierModuleData j hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i)) : (X'.toGradedCartierModuleData j hc').NMod) = (X'.toGradedCartierModuleData j hc').nMk (Θ m, 0) := by
    intro m hm
    have hminv : m ∈ (CritChart.invariants X j (i : ℕ)) := (hetaInv m).1 hm
    have h1 := hθ₀f_eq ⟨m, hminv⟩
    have h2 : Θ m = θ₀f ⟨m, hminv⟩ := hΘinv ⟨m, hminv⟩
    rw [h2, ← h1]

  have hdesc := CerednikDrinfeld.FormalODModule.apply_mkQ_eq_mkQ_and_mem_vRange_iff_of_apply_eq_nMk_of_isCritical_of_isAlgClosed
    p K j X X' hX hX4 hX' hX'4 hc hc' L hL L' hL' i hi θη τ hτ hcompat Θ hΘ

  have hcP : IsCompl (X.gradedSubmodule j (i : ℕ)) (X.gradedSubmodule j ((i : ℕ) + 1)) := by
    fin_cases i
    · exact (isCompl_gradedSubmodule_iff X j 0 1).2 hc
    · show IsCompl (X.gradedSubmodule j 1) (X.gradedSubmodule j (0 + 2))
      rw [gradedSubmodule_add_two]; exact ((isCompl_gradedSubmodule_iff X j 0 1).2 hc).symm
  have hcP' : IsCompl (X'.gradedSubmodule j (i : ℕ)) (X'.gradedSubmodule j ((i : ℕ) + 1)) := by
    fin_cases i
    · exact (isCompl_gradedSubmodule_iff X' j 0 1).2 hc'
    · show IsCompl (X'.gradedSubmodule j 1) (X'.gradedSubmodule j (0 + 2))
      rw [gradedSubmodule_add_two]; exact ((isCompl_gradedSubmodule_iff X' j 0 1).2 hc').symm
  have hP2 : X.gradedPiece j ((i : ℕ) + 1 + 1) = X.gradedPiece j (i : ℕ) := gradedPiece_add_two X j (i : ℕ)
  have hP2' : X'.gradedPiece j ((i : ℕ) + 1 + 1) = X'.gradedPiece j (i : ℕ) := gradedPiece_add_two X' j (i : ℕ)

  have hV01 : ∀ x ∈ X.gradedPiece j (i : ℕ), verschiebungInt x ∈ X.gradedPiece j ((i : ℕ) + 1) :=
    fun x hx => verschiebungInt_mem_gradedPiece_succ X j _ x hx
  have hV10 : ∀ y ∈ X.gradedPiece j ((i : ℕ) + 1), verschiebungInt y ∈ X.gradedPiece j (i : ℕ) :=
    fun y hy => hP2 ▸ verschiebungInt_mem_gradedPiece_succ X j _ y hy
  have hV01' : ∀ x ∈ X'.gradedPiece j (i : ℕ), verschiebungInt x ∈ X'.gradedPiece j ((i : ℕ) + 1) :=
    fun x hx => verschiebungInt_mem_gradedPiece_succ X' j _ x hx
  have hV10' : ∀ y ∈ X'.gradedPiece j ((i : ℕ) + 1), verschiebungInt y ∈ X'.gradedPiece j (i : ℕ) :=
    fun y hy => hP2' ▸ verschiebungInt_mem_gradedPiece_succ X' j _ y hy
  have hPi01 : ∀ x ∈ X.gradedPiece j (i : ℕ), endAct X.varpiEnd x ∈ X.gradedPiece j ((i : ℕ) + 1) :=
    fun x hx => endAct_varpiEnd_mem_gradedPiece_succ X j _ x hx
  have hPi10 : ∀ y ∈ X.gradedPiece j ((i : ℕ) + 1), endAct X.varpiEnd y ∈ X.gradedPiece j (i : ℕ) :=
    fun y hy => hP2 ▸ endAct_varpiEnd_mem_gradedPiece_succ X j _ y hy
  have hPi01' : ∀ x ∈ X'.gradedPiece j (i : ℕ), endAct X'.varpiEnd x ∈ X'.gradedPiece j ((i : ℕ) + 1) :=
    fun x hx => endAct_varpiEnd_mem_gradedPiece_succ X' j _ x hx
  have hPi10' : ∀ y ∈ X'.gradedPiece j ((i : ℕ) + 1), endAct X'.varpiEnd y ∈ X'.gradedPiece j (i : ℕ) :=
    fun y hy => hP2' ▸ endAct_varpiEnd_mem_gradedPiece_succ X' j _ y hy

  have hVinj : Function.Injective (verschiebungInt : (CartierModule p X.F) → (CartierModule p X.F)) := by
    intro a b hab
    have h1 : (p : ℕ) • a = (p : ℕ) • b := by rw [← frobenius_verschiebungInt, ← frobenius_verschiebungInt, hab]
    have h2 : endAct X.varpiEnd (endAct X.varpiEnd (a - b)) = 0 := by
      rw [endAct_varpiEnd_endAct_varpiEnd, smul_sub, h1, sub_self]
    exact sub_eq_zero.1 (htors _ (htors _ h2))
  have hVinj' : Function.Injective (verschiebungInt : (CartierModule p X'.F) → (CartierModule p X'.F)) := by
    intro a b hab
    have h1 : (p : ℕ) • a = (p : ℕ) • b := by rw [← frobenius_verschiebungInt, ← frobenius_verschiebungInt, hab]
    have h2 : endAct X'.varpiEnd (endAct X'.varpiEnd (a - b)) = 0 := by
      rw [endAct_varpiEnd_endAct_varpiEnd, smul_sub, h1, sub_self]
    exact sub_eq_zero.1 (htors' _ (htors' _ h2))
  have hp1 : (WittVector.verschiebung (1 : (WittVector p K)) : (WittVector p K)) = (p : (WittVector p K)) := by
    have := WittVector.verschiebung_frobenius (1 : (WittVector p K))
    rwa [map_one, one_mul] at this
  have hVF : ∀ g : (CartierModule p X.F), verschiebungInt (frobenius g) = (p : ℕ) • g := by
    intro g
    rw [← one_smul (WittVector p K) (frobenius g), verschiebungInt_smul_frobenius, hp1, natCast_smul_eq_nsmul']
  have hVF' : ∀ g : (CartierModule p X'.F), verschiebungInt (frobenius g) = (p : ℕ) • g := by
    intro g
    rw [← one_smul (WittVector p K) (frobenius g), verschiebungInt_smul_frobenius, hp1, natCast_smul_eq_nsmul']

  have hdeg' : ∀ z : (CartierModule p X'.F), verschiebungInt z ∈ X'.gradedPiece j (i : ℕ) → z ∈ X'.gradedPiece j ((i : ℕ) + 1) := by
    intro z hz
    obtain ⟨z₀, hz₀, z₁, hz₁, hzz⟩ := Submodule.mem_sup.1 (hcP'.sup_eq_top.symm ▸ Submodule.mem_top (x := z))
    have h0 : verschiebungInt z₀ ∈ (X'.gradedSubmodule j (i : ℕ)) ⊓ (X'.gradedSubmodule j ((i : ℕ) + 1)) := by
      refine ⟨?_, hV01' z₀ hz₀⟩
      have : verschiebungInt z₀ = verschiebungInt z - verschiebungInt z₁ := by rw [← hzz, map_add, add_sub_cancel_right]
      rw [this]
      exact Submodule.sub_mem _ hz (hV10' z₁ hz₁)
    rw [hcP'.inf_eq_bot, Submodule.mem_bot] at h0
    have : z₀ = 0 := hVinj' (by rw [h0, map_zero])
    rw [← hzz, this, zero_add]; exact hz₁
  have hdeg : ∀ z : (CartierModule p X.F), verschiebungInt z ∈ X.gradedPiece j (i : ℕ) → z ∈ X.gradedPiece j ((i : ℕ) + 1) := by
    intro z hz
    obtain ⟨z₀, hz₀, z₁, hz₁, hzz⟩ := Submodule.mem_sup.1 (hcP.sup_eq_top.symm ▸ Submodule.mem_top (x := z))
    have h0 : verschiebungInt z₀ ∈ (X.gradedSubmodule j (i : ℕ)) ⊓ (X.gradedSubmodule j ((i : ℕ) + 1)) := by
      refine ⟨?_, hV01 z₀ hz₀⟩
      have : verschiebungInt z₀ = verschiebungInt z - verschiebungInt z₁ := by rw [← hzz, map_add, add_sub_cancel_right]
      rw [this]
      exact Submodule.sub_mem _ hz (hV10 z₁ hz₁)
    rw [hcP.inf_eq_bot, Submodule.mem_bot] at h0
    have : z₀ = 0 := hVinj (by rw [h0, map_zero])
    rw [← hzz, this, zero_add]; exact hz₁

  have hΘmem : ∀ x ∈ X.gradedPiece j (i : ℕ), Θ x ∈ X'.gradedPiece j (i : ℕ) := fun x hx => hΘbij.mapsTo hx
  have hΘinj : ∀ x ∈ X.gradedPiece j (i : ℕ), ∀ y ∈ X.gradedPiece j (i : ℕ), Θ x = Θ y → x = y :=
    fun x hx y hy h => hΘbij.injOn hx hy h
  have hΘsurj : ∀ x' ∈ X'.gradedPiece j (i : ℕ), ∃ x ∈ X.gradedPiece j (i : ℕ), Θ x = x' := fun x' hx' => by
    obtain ⟨x, hx, h⟩ := hΘbij.surjOn hx'; exact ⟨x, hx, h⟩
  obtain ⟨e, heinv, heb, -, -, -⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical
      p j (⟨X, hX, hX4⟩ : CerednikDrinfeld.SpecialFormalODModule p j) (i : ℕ) hicrit
  have he0 : ∀ r, e r ∈ X.gradedPiece j (i : ℕ) := fun r => (heinv r).1
  have hePV : ∀ r, endAct X.varpiEnd (e r) = verschiebungInt (e r) := fun r => by rw [hV]; exact (heinv r).2
  have hΘe : ∀ r, endAct X'.varpiEnd (Θ (e r)) = verschiebungInt (Θ (e r)) := fun r => by
    have h2 := (θ₀ ⟨e r, heinv r⟩).2.2
    have h3 : ((θ₀ ⟨e r, heinv r⟩ : (CritChart.invariants X' j (i : ℕ))) : (CartierModule p X'.F)) = Θ (e r) := (hΘinv ⟨e r, heinv r⟩).symm
    rw [h3] at h2
    rw [hV']; exact h2
  have hVVe : ∀ r, verschiebungInt (verschiebungInt (e r)) = (p : ℕ) • e r := fun r => by
    rw [← hePV r, ← endAct_verschiebungInt, ← hePV r, endAct_varpiEnd_endAct_varpiEnd]
  have hVVe' : ∀ r, verschiebungInt (verschiebungInt (Θ (e r))) = (p : ℕ) • Θ (e r) := fun r => by
    rw [← hΘe r, ← endAct_verschiebungInt, ← hΘe r, endAct_varpiEnd_endAct_varpiEnd]

  have hσ : Function.Surjective (WittVector.frobenius : (WittVector p K) → (WittVector p K)) := (WittVector.frobenius_bijective p K).2

  have hexp2 : ∀ x ∈ X.gradedPiece j (i : ℕ), ∃ u : Fin 2 → (WittVector p K),
      x = ∑ r, WittVector.frobenius (WittVector.frobenius (u r)) • e r := by
    intro x hx
    obtain ⟨w, hw, -⟩ := heb x hx
    choose u1 hu1 using fun r => hσ (w r)
    choose u2 hu2 using fun r => hσ (u1 r)
    refine ⟨u2, ?_⟩
    rw [hw]; congr 1; ext r; rw [hu2, hu1]

  have hΘVV : ∀ x ∈ X.gradedPiece j (i : ℕ),
      Θ (verschiebungInt (verschiebungInt x)) = verschiebungInt (verschiebungInt (Θ x)) := by
    intro x hx
    obtain ⟨u, rfl⟩ := hexp2 x hx
    have h1 : verschiebungInt (verschiebungInt (∑ r, WittVector.frobenius (WittVector.frobenius (u r)) • e r)) =
        ∑ r, u r • ((p : ℕ) • e r) := by
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [← hVVe r, smul_verschiebungInt, smul_verschiebungInt]
    have h2 : verschiebungInt (verschiebungInt (Θ (∑ r, WittVector.frobenius (WittVector.frobenius (u r)) • e r))) =
        ∑ r, u r • ((p : ℕ) • Θ (e r)) := by
      rw [map_sum, map_sum, map_sum]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [map_smul, ← hVVe' r, smul_verschiebungInt, smul_verschiebungInt]
    rw [h1, h2, map_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [map_smul, map_nsmul]
  have hexp1 : ∀ x ∈ X.gradedPiece j (i : ℕ), ∃ u : Fin 2 → (WittVector p K), x = ∑ r, WittVector.frobenius (u r) • e r := by
    intro x hx
    obtain ⟨w, hw, -⟩ := heb x hx
    choose u1 hu1 using fun r => hσ (w r)
    refine ⟨u1, ?_⟩
    rw [hw]; exact Finset.sum_congr rfl fun r _ => by rw [hu1]

  have hΘPiV : ∀ x ∈ X.gradedPiece j (i : ℕ),
      Θ (endAct X.varpiEnd (verschiebungInt x)) = endAct X'.varpiEnd (verschiebungInt (Θ x)) := by
    intro x hx
    obtain ⟨u, rfl⟩ := hexp1 x hx
    have h1 : endAct X.varpiEnd (verschiebungInt (∑ r, WittVector.frobenius (u r) • e r)) = ∑ r, u r • ((p : ℕ) • e r) := by
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [← smul_verschiebungInt, endAct_smul_witt, ← hePV r, endAct_varpiEnd_endAct_varpiEnd]
    have h2 : endAct X'.varpiEnd (verschiebungInt (Θ (∑ r, WittVector.frobenius (u r) • e r))) = ∑ r, u r • ((p : ℕ) • Θ (e r)) := by
      rw [map_sum, map_sum, map_sum]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [map_smul, ← smul_verschiebungInt, endAct_smul_witt, ← hΘe r, endAct_varpiEnd_endAct_varpiEnd]
    rw [h1, h2, map_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [map_smul, map_nsmul]

  have hex1 : ∀ y ∈ X.gradedPiece j ((i : ℕ) + 1), ∃ y' : (CartierModule p X'.F), verschiebungInt y' = Θ (verschiebungInt y) := by
    intro y hy
    exact ((hdesc (verschiebungInt y) (hV10 y hy)).2).1 ⟨y, rfl⟩
  obtain ⟨Θ₁, hΘ₁⟩ := CritExtendBlocks.vLift p K j X X' hVinj' Θ ((i : ℕ) + 1) hex1
  let π₀ : (CartierModule p X.F) →ₗ[(WittVector p K)] (X.gradedSubmodule j (i : ℕ)) := Submodule.projectionOnto (X.gradedSubmodule j (i : ℕ)) (X.gradedSubmodule j ((i : ℕ) + 1)) hcP
  let π₁ : (CartierModule p X.F) →ₗ[(WittVector p K)] (X.gradedSubmodule j ((i : ℕ) + 1)) := Submodule.projectionOnto (X.gradedSubmodule j ((i : ℕ) + 1)) (X.gradedSubmodule j (i : ℕ)) hcP.symm
  have hsum : ∀ f : (CartierModule p X.F), ((π₀ f : (CartierModule p X.F)) + (π₁ f : (CartierModule p X.F))) = f := fun f =>
    Submodule.projection_add_projection_eq_self hcP f
  let θl : (CartierModule p X.F) →ₗ[(WittVector p K)] (CartierModule p X'.F) := Θ.comp ((X.gradedSubmodule j (i : ℕ)).subtype.comp π₀) + Θ₁.comp π₁
  have hθl : ∀ f : (CartierModule p X.F), θl f = Θ (π₀ f : (CartierModule p X.F)) + Θ₁ (π₁ f) := fun f => rfl
  have hθ0 : ∀ x (hx : x ∈ X.gradedPiece j (i : ℕ)), θl x = Θ x := by
    intro x hx
    have h0 : π₀ x = ⟨x, hx⟩ := Submodule.projectionOnto_apply_left hcP ⟨x, hx⟩
    have h1 : π₁ x = 0 := Submodule.projectionOnto_apply_right hcP.symm ⟨x, hx⟩
    rw [hθl, h0, h1, map_zero, add_zero]
  have hθ1 : ∀ y (hy : y ∈ X.gradedPiece j ((i : ℕ) + 1)), θl y = Θ₁ ⟨y, hy⟩ := by
    intro y hy
    have h0 : π₀ y = 0 := Submodule.projectionOnto_apply_right hcP ⟨y, hy⟩
    have h1 : π₁ y = ⟨y, hy⟩ := Submodule.projectionOnto_apply_left hcP.symm ⟨y, hy⟩
    rw [hθl, h0, h1, Submodule.coe_zero, map_zero, zero_add]
  have hθ1V : ∀ y (hy : y ∈ X.gradedPiece j ((i : ℕ) + 1)), verschiebungInt (θl y) = Θ (verschiebungInt y) := by
    intro y hy; rw [hθ1 y hy]; exact hΘ₁ ⟨y, hy⟩
  have hmem0 : ∀ f : (CartierModule p X.F), (π₀ f : (CartierModule p X.F)) ∈ X.gradedPiece j (i : ℕ) := fun f => (π₀ f).2
  have hmem1 : ∀ f : (CartierModule p X.F), (π₁ f : (CartierModule p X.F)) ∈ X.gradedPiece j ((i : ℕ) + 1) := fun f => (π₁ f).2

  have hθP0 : ∀ x ∈ X.gradedPiece j (i : ℕ), θl x ∈ X'.gradedPiece j (i : ℕ) := fun x hx => by
    rw [hθ0 x hx]; exact hΘmem x hx
  have hθP1 : ∀ y ∈ X.gradedPiece j ((i : ℕ) + 1), θl y ∈ X'.gradedPiece j ((i : ℕ) + 1) := fun y hy => by
    apply hdeg'
    rw [hθ1V y hy]
    exact hΘmem _ (hV10 y hy)

  have hVc : ∀ f : (CartierModule p X.F), θl (verschiebungInt f) = verschiebungInt (θl f) := by
    intro f
    have ha : θl (verschiebungInt (π₀ f : (CartierModule p X.F))) = verschiebungInt (θl (π₀ f : (CartierModule p X.F))) := by
      apply hVinj'
      rw [hθ1V _ (hV01 _ (hmem0 f)), hΘVV _ (hmem0 f), hθ0 _ (hmem0 f)]
    have hb : θl (verschiebungInt (π₁ f : (CartierModule p X.F))) = verschiebungInt (θl (π₁ f : (CartierModule p X.F))) := by
      rw [hθ0 _ (hV10 _ (hmem1 f)), hθ1V _ (hmem1 f)]
    conv_lhs => rw [← hsum f]
    conv_rhs => rw [← hsum f]
    rw [map_add, map_add, ha, hb, map_add, map_add]

  have hPic0 : ∀ x ∈ X.gradedPiece j (i : ℕ), θl (endAct X.varpiEnd x) = endAct X'.varpiEnd (θl x) := by
    intro x hx
    apply hVinj'
    rw [hθ1V _ (hPi01 x hx), ← endAct_verschiebungInt, hΘPiV x hx, hθ0 x hx, endAct_verschiebungInt]
  have hPic1 : ∀ y ∈ X.gradedPiece j ((i : ℕ) + 1), θl (endAct X.varpiEnd y) = endAct X'.varpiEnd (θl y) := by
    intro y hy
    apply hVinj'
    rw [← hVc, ← endAct_verschiebungInt, hPic0 _ (hV10 _ hy), hVc, endAct_verschiebungInt]
  have hPic : ∀ f : (CartierModule p X.F), θl (endAct X.varpiEnd f) = endAct X'.varpiEnd (θl f) := by
    intro f
    conv_lhs => rw [← hsum f]
    conv_rhs => rw [← hsum f]
    rw [map_add, map_add, hPic0 _ (hmem0 f), hPic1 _ (hmem1 f), map_add, map_add]

  have hFc : ∀ f : (CartierModule p X.F), θl (frobenius f) = frobenius (θl f) := by
    intro f
    apply hVinj'
    rw [← hVc, hVF, hVF', map_nsmul]

  have hKnil : IsNilpotent ((p : ℕ) : K) := ⟨1, by rw [pow_one]; exact CharP.cast_eq_zero K p⟩
  have hTe := CritExtendBlocks.teich_comm p K j X X' (i : ℕ) hcP θl hθP0 hθP1
  have hAct := CerednikDrinfeld.FormalODModule.endAct_actEnd_comp_eq_of_forall_teichmuller_of_isNilpotent
    p hKnil X X' θl.toAddMonoidHom hTe

  have hdisj' : ∀ a ∈ X'.gradedPiece j (i : ℕ), ∀ b ∈ X'.gradedPiece j ((i : ℕ) + 1), a + b = 0 → a = 0 ∧ b = 0 := by
    intro a ha b hb hab
    have ha' : a ∈ (X'.gradedSubmodule j (i : ℕ)) ⊓ (X'.gradedSubmodule j ((i : ℕ) + 1)) := by
      refine ⟨ha, ?_⟩
      have : a = -b := eq_neg_of_add_eq_zero_left hab
      rw [this]; exact Submodule.neg_mem _ hb
    rw [hcP'.inf_eq_bot, Submodule.mem_bot] at ha'
    refine ⟨ha', ?_⟩
    rwa [ha', zero_add] at hab
  have hInj : Function.Injective θl := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro f hf
    rw [LinearMap.mem_ker, hθl] at hf
    obtain ⟨h0, h1⟩ := hdisj' _ (hΘmem _ (hmem0 f)) _ (by rw [← hθ1 _ (hmem1 f)]; exact hθP1 _ (hmem1 f)) hf
    have hf0 : (π₀ f : (CartierModule p X.F)) = 0 := hΘinj _ (hmem0 f) 0 (zero_mem _) (by rw [h0, map_zero])
    have hf1 : (π₁ f : (CartierModule p X.F)) = 0 := by
      apply hVinj
      rw [map_zero]
      apply hΘinj _ (hV10 _ (hmem1 f)) 0 (zero_mem _)
      rw [map_zero, ← hΘ₁, h1, map_zero]
    rw [← hsum f, hf0, hf1, add_zero]
  have hSurj : Function.Surjective θl := by
    intro g
    obtain ⟨g₀, hg₀, g₁, hg₁, hgg⟩ := Submodule.mem_sup.1 (hcP'.sup_eq_top.symm ▸ Submodule.mem_top (x := g))
    obtain ⟨x₀, hx₀, hx₀e⟩ := hΘsurj g₀ hg₀

    obtain ⟨x, hx, hxe⟩ := hΘsurj _ (hV10' g₁ hg₁)
    obtain ⟨y, hy⟩ := ((hdesc x hx).2).2 ⟨g₁, hxe.symm⟩
    have hy1 : y ∈ X.gradedPiece j ((i : ℕ) + 1) := hdeg y (hy.symm ▸ hx)
    refine ⟨x₀ + y, ?_⟩
    rw [map_add, hθ0 x₀ hx₀, hx₀e, ← hgg]
    congr 1
    apply hVinj'
    rw [hθ1V y hy1, hy, hxe]

  refine ⟨θl.toAddMonoidHom, ⟨hInj, hSurj⟩, hFc, hVc, fun w f => θl.map_smul w f, hAct, hPic, ?_⟩
  intro m hm
  have hm0 : m ∈ X.gradedPiece j (i : ℕ) := ((hetaInv m).1 hm).1
  show _ = (X'.toGradedCartierModuleData j hc').nMk (θl m, 0)
  rw [hθ0 m hm0]
  exact hΘ m hm

set_option maxHeartbeats 3200000 in
open CritExtendAsm MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.GradedCartierModuleData CerednikDrinfeld.FormalODModule in

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0)
      (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hLΦ : ∃ L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod,
      (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {κ : Type} [Field κ] [IsAlgClosed κ] [CharP κ p] [Algebra ℤ_[p] κ] (ψ : WittVector p k →+* κ)
    (t t' : Rigidified p Φ κ) (ht : t.IsAdmissible ι ψ) (ht' : t'.IsAdmissible ι ψ)
    (Q Q' : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) κ)
    (hQ : t.IsCartierQuadruple ι hcΦ rΦ ψ Q) (hQ' : t'.IsCartierQuadruple ι hcΦ rΦ ψ Q')
    (hiso : Q.IsIsomorphic Q')
    (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ) (hOD' : FormalODModule.IsODHom (t'.Φbar ψ) t'.Xbar t'.ρ)
    (hc : t.IsGradedS ι ψ (Rigidified.awayHom (1 : κ))) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom (1 : κ)))
    (hc' : t'.IsGradedS ι ψ (Rigidified.awayHom (1 : κ))) (hcb' : t'.IsGradedSbar ι ψ (Rigidified.awayHom (1 : κ)))
    (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom (1 : κ)))
    (L : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).M →+ ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).NMod) (hL : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).IsCanonicalLMap L)
    (L' : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').M →+ ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').NMod) (hL' : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').IsCanonicalLMap L')
    (i : Fin 2)
    (hi : ∀ m ∈ (t.XS (Rigidified.awayHom (1 : κ))).gradedPiece (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) (i : ℕ), ∃ y : MvFormalGroup.CartierModule p (t.XS (Rigidified.awayHom (1 : κ))).F,
        MvFormalGroup.CartierModule.verschiebungInt y = MvFormalGroup.CartierModule.endAct (t.XS (Rigidified.awayHom (1 : κ))).varpiEnd m)
    (hi' : ∀ m ∈ (t'.XS (Rigidified.awayHom (1 : κ))).gradedPiece (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) (i : ℕ), ∃ y : MvFormalGroup.CartierModule p (t'.XS (Rigidified.awayHom (1 : κ))).F,
        MvFormalGroup.CartierModule.verschiebungInt y = MvFormalGroup.CartierModule.endAct (t'.XS (Rigidified.awayHom (1 : κ))).varpiEnd m)
    (θη : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).etaPiece L hL.isCartierLMap.map_verschiebung i →+ ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i)
    (τ : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).LieQuot →ₗ[WittVector p (Rigidified.Baway (1 : κ))] ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').LieQuot)
    (hθη : Function.Bijective θη) (hτ : Function.Injective τ)
    (hcompat : ∀ (m : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).M) (m' : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').M) (hm : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).nMk (m, 0) ∈ ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).etaPiece L hL.isCartierLMap.map_verschiebung i),
        ((θη ⟨((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).nMk (m, 0), hm⟩ : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i) : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').NMod) = ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').nMk (m', 0) →
        τ (((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).vRange.mkQ m) = ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').vRange.mkQ m') :
    ∃ θ : MvFormalGroup.CartierModule p (t.XS (Rigidified.awayHom (1 : κ))).F →+ MvFormalGroup.CartierModule p (t'.XS (Rigidified.awayHom (1 : κ))).F,
      Function.Bijective θ ∧
      (∀ f, θ (MvFormalGroup.CartierModule.frobenius f) = MvFormalGroup.CartierModule.frobenius (θ f)) ∧
      (∀ f, θ (MvFormalGroup.CartierModule.verschiebungInt f) = MvFormalGroup.CartierModule.verschiebungInt (θ f)) ∧
      (∀ (w : WittVector p (Rigidified.Baway (1 : κ))) f, θ (w • f) = w • θ f) ∧
      (∀ (a : Zp2 p) f, θ (MvFormalGroup.CartierModule.endAct ((t.XS (Rigidified.awayHom (1 : κ))).actEnd a) f) =
        MvFormalGroup.CartierModule.endAct ((t'.XS (Rigidified.awayHom (1 : κ))).actEnd a) (θ f)) ∧
      (∀ f, θ (MvFormalGroup.CartierModule.endAct (t.XS (Rigidified.awayHom (1 : κ))).varpiEnd f) =
        MvFormalGroup.CartierModule.endAct (t'.XS (Rigidified.awayHom (1 : κ))).varpiEnd (θ f)) ∧
      (∀ (m : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).M) (hm : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).nMk (m, 0) ∈ ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).etaPiece L hL.isCartierLMap.map_verschiebung i),
        ((θη ⟨((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).nMk (m, 0), hm⟩ : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i) : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').NMod) = ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').nMk (θ m, 0)) := by
  classical
  let eS : κ ≃+* (Rigidified.Baway (1 : κ)) := (IsLocalization.atOne κ (Rigidified.Baway (1 : κ))).toRingEquiv
  letI instF : Field (Rigidified.Baway (1 : κ)) := (MulEquiv.isField (Field.toIsField κ) eS.symm.toMulEquiv).toField
  haveI : CharP (Rigidified.Baway (1 : κ)) p := charP_of_injective_ringHom (f := eS.toRingHom) (fun a b h => eS.injective h) p
  haveI : IsAlgClosed (Rigidified.Baway (1 : κ)) := isAlgClosed_of_ringEquiv eS
  have hXS : (t.XS (Rigidified.awayHom (1 : κ))).IsSpecial (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) := CerednikDrinfeld.FormalODModule.IsSpecial.map _ (Rigidified.awayHom (1 : κ)) t.X ht.1
  have hXS' : (t'.XS (Rigidified.awayHom (1 : κ))).IsSpecial (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) := CerednikDrinfeld.FormalODModule.IsSpecial.map _ (Rigidified.awayHom (1 : κ)) t'.X ht'.1
  have hX4S : (t.XS (Rigidified.awayHom (1 : κ))).HasHeight 4 := hasHeight_map_field t.X ht.2.1 (Rigidified.awayHom (1 : κ))
  have hX4S' : (t'.XS (Rigidified.awayHom (1 : κ))).HasHeight 4 := hasHeight_map_field t'.X ht'.2.1 (Rigidified.awayHom (1 : κ))
  exact CritExtendAsm.assemble p (Rigidified.Baway (1 : κ)) (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) (t.XS (Rigidified.awayHom (1 : κ))) (t'.XS (Rigidified.awayHom (1 : κ))) hXS hX4S hXS' hX4S' hc hc' L hL L' hL' i hi hi'
    θη τ hθη hτ hcompat

end S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_bijective_cartierModule_XS_awayHom_of_etaPiece_bijective_of_isAlgClosed_of_lieZero_le_ker
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_bijective_cartierModule_XS_awayHom_of_etaPiece_bijective_of_isAlgClosed_of_lieZero_le_ker (solution)
