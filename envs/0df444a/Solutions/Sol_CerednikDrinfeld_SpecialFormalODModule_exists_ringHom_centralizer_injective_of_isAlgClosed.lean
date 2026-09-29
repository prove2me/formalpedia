-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.exists_ringHom_centralizer_injective_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/57562023-3730-5275-81b0-6314c9985149

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_addMonoidHom_cartierModule_injective_of_isAlgClosed
import Theorems.Thm_MvFormalGroup_CartierModule_exists_hom_map_eq_of_perfectRing
import Theorems.Thm_MvFormalGroup_CartierModule_eq_of_map_eq
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_forall_nsmul_eq_zero_imp_and_exists_ringHom_centralizer_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_ringHom_centralizer_injective_of_isAlgClosed
p2m_attr_erase "instance" "MvFormalGroup.CartierModule.instModuleWittVector instTopologicallyFGOfFiniteType MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup CerednikDrinfeld.LubinTate.instIsCommMap CerednikDrinfeld.LubinTate.instFintypeGaloisFieldTwo CerednikDrinfeld.LubinTate.sigma_isComm CerednikDrinfeld.LubinTate.sigmaBar_isComm CerednikDrinfeld.BoxBasisLemma.instDecidableInBox CerednikDrinfeld.Standard.law_isComm"
p2m_attr_erase "simp" "MvFormalGroup.WittLaw.verPoly_succ MvFormalGroup.WittLaw.xVec_coeff MvFormalGroup.WittLaw.cVec_coeff MvFormalGroup.WittLaw.cVec_mul MvFormalGroup.WittLaw.mulFam_apply MvFormalGroup.CartierModule.mapLinear_apply MvFormalGroup.WittLaw.cVec_add MvFormalGroup.WittLaw.cVec_zero MvFormalGroup.WittLaw.verPoly_zero MvFormalGroup.CartierModule.toPowerSeries_wittSMul MvFormalGroup.CartierModule.toPowerSeries_smul_witt MvFormalGroup.WittLaw.cVec_one MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec CerednikDrinfeld.Standard.emb_inr CerednikDrinfeld.BoxBasisLemma.toFinsupp_apply CerednikDrinfeld.Standard.chi_zero CerednikDrinfeld.Standard.emb_inl CerednikDrinfeld.Standard.chi_one"

set_option autoImplicit false

noncomputable section

universe u

namespace P2mKcK2cAssembly

section QuasiInverse

variable {M M' : Type*} [AddCommGroup M] [AddCommGroup M']

def quasiInv (θ : M →+ M') (hinj : Function.Injective θ) (c : ℕ) (hc : ∀ g, ∃ f, θ f = c • g) :
    M' →+ M where
  toFun g := Classical.choose (hc g)
  map_zero' := hinj (by rw [Classical.choose_spec (hc 0), smul_zero, map_zero])
  map_add' g g' := hinj (by
    rw [Classical.choose_spec (hc _), map_add, Classical.choose_spec (hc g),
      Classical.choose_spec (hc g'), smul_add])

theorem apply_quasiInv (θ : M →+ M') (hinj : Function.Injective θ) (c : ℕ)
    (hc : ∀ g, ∃ f, θ f = c • g) (g : M') : θ (quasiInv θ hinj c hc g) = c • g :=
  Classical.choose_spec (hc g)

theorem quasiInv_apply (θ : M →+ M') (hinj : Function.Injective θ) (c : ℕ)
    (hc : ∀ g, ∃ f, θ f = c • g) (f : M) : quasiInv θ hinj c hc (θ f) = c • f :=
  hinj (by rw [apply_quasiInv, map_nsmul])

theorem quasiInv_comm (θ : M →+ M') (hinj : Function.Injective θ) (c : ℕ)
    (hc : ∀ g, ∃ f, θ f = c • g) (T : M →+ M) (T' : M' →+ M') (hT : ∀ f, θ (T f) = T' (θ f))
    (g : M') : quasiInv θ hinj c hc (T' g) = T (quasiInv θ hinj c hc g) :=
  hinj (by rw [apply_quasiInv, hT, apply_quasiInv, map_nsmul])

end QuasiInverse

open CerednikDrinfeld MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {k : Type u} [Field k] [CharP k p]

omit [CharP k p] in
theorem map_mul_end {d : ℕ} {G : MvFormalGroup d k} [G.IsComm] (φ ψ : MvFormalGroup.End G)
    (f : MvFormalGroup.CartierModule p G) : map (φ * ψ) f = map φ (map ψ f) :=
  map_comp φ ψ f

omit [CharP k p] in
theorem map_one_end {d : ℕ} {G : MvFormalGroup d k} [G.IsComm]
    (f : MvFormalGroup.CartierModule p G) : map (1 : MvFormalGroup.End G) f = f :=
  map_id f

omit [CharP k p] in
theorem map_natCast_end {d : ℕ} {G : MvFormalGroup d k} [G.IsComm] (n : ℕ)
    (f : MvFormalGroup.CartierModule p G) : map ((n : MvFormalGroup.End G)) f = n • f :=
  endAct_natCast n f

omit [CharP k p] in
theorem map_zero_end {d : ℕ} {G : MvFormalGroup d k} [G.IsComm]
    (f : MvFormalGroup.CartierModule p G) : map (0 : MvFormalGroup.End G) f = 0 :=
  map_zero_hom f

omit [CharP k p] in
theorem map_add_end {d : ℕ} {G : MvFormalGroup d k} [G.IsComm] (φ ψ : MvFormalGroup.End G)
    (f : MvFormalGroup.CartierModule p G) : map (φ + ψ) f = map φ f + map ψ f :=
  map_add_hom φ ψ f

theorem hom_eq {d d' : ℕ} {G : MvFormalGroup d k} {G' : MvFormalGroup d' k} [G.IsComm] [G'.IsComm]
    (φ ψ : G.Hom G') (h : ∀ f : MvFormalGroup.CartierModule p G, map φ f = map ψ f) : φ = ψ :=
  MvFormalGroup.CartierModule.eq_of_map_eq p G G' φ ψ h

omit hp [CharP k p] in

theorem pow_torsionFree {M : Type*} [AddCommGroup M] (hM : ∀ f : M, p • f = 0 → f = 0) :
    ∀ (n : ℕ) (f : M), p ^ n • f = 0 → f = 0 := by
  intro n
  induction n with
  | zero => intro f hf; simpa using hf
  | succ n ih =>
    intro f hf
    rw [pow_succ, mul_smul] at hf
    exact hM f (ih (p • f) hf)

omit [CharP k p] in

theorem natCast_mul_matrix (n : ℕ) (X : Matrix (Fin 2) (Fin 2) ℚ_[p]) :
    (n : Matrix (Fin 2) (Fin 2) ℚ_[p]) * X = (n : ℚ_[p]) • X := by
  rw [← nsmul_eq_mul, Nat.cast_smul_eq_nsmul]

theorem main [IsAlgClosed k] (jj : Zp2 p →+* k) (Φ : SpecialFormalODModule p jj) :
    ∃ θ : Subring.centralizer
          (Set.range Φ.toFormalODModule.actEnd ∪ {Φ.toFormalODModule.varpiEnd}) →+*
        Matrix (Fin 2) (Fin 2) ℚ_[p],
      Function.Injective θ ∧
      ∃ m : ℕ,
        (∀ M : Matrix (Fin 2) (Fin 2) ℤ_[p],
          ∃ e, θ e = (p : ℚ_[p]) ^ m • M.map ((↑) : ℤ_[p] → ℚ_[p])) ∧
        (∀ e, ∃ M : Matrix (Fin 2) (Fin 2) ℤ_[p],
          (p : ℚ_[p]) ^ m • θ e = M.map ((↑) : ℤ_[p] → ℚ_[p])) := by
  classical

  obtain ⟨Φ₀, hTF₀, θ₀, hθ₀, m₀, hS1, hS2⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_forall_nsmul_eq_zero_imp_and_exists_ringHom_centralizer_injective
      p k jj

  obtain ⟨θ, hinj, hF, hV, hH, hAct, hPi, N, hN⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_addMonoidHom_cartierModule_injective_of_isAlgClosed
      p k jj Φ Φ₀
  set θ' := quasiInv θ hinj (p ^ N) hN with hθ'
  have hθθ' : ∀ g, θ (θ' g) = p ^ N • g := apply_quasiInv θ hinj _ hN
  have hθ'θ : ∀ f, θ' (θ f) = p ^ N • f := quasiInv_apply θ hinj _ hN
  have hAct' : ∀ (a : Zp2 p) g, θ' (endAct (Φ₀.actEnd a) g) = endAct (Φ.actEnd a) (θ' g) :=
    fun a g => quasiInv_comm θ hinj _ hN (endAct (Φ.actEnd a)) (endAct (Φ₀.actEnd a)) (hAct a) g
  have hPi' : ∀ g, θ' (endAct Φ₀.varpiEnd g) = endAct Φ.varpiEnd (θ' g) :=
    fun g => quasiInv_comm θ hinj _ hN (endAct Φ.varpiEnd) (endAct Φ₀.varpiEnd) hPi g

  obtain ⟨ρ, hρ⟩ :=
    MvFormalGroup.CartierModule.exists_hom_map_eq_of_perfectRing p Φ.F Φ₀.F θ hF hV hH
  obtain ⟨ρ', hρ'⟩ := MvFormalGroup.CartierModule.exists_hom_map_eq_of_perfectRing p Φ₀.F Φ.F θ'
    (fun g => quasiInv_comm θ hinj _ hN frobenius frobenius hF g)
    (fun g => quasiInv_comm θ hinj _ hN verschiebung verschiebung hV g)
    (fun a g => quasiInv_comm θ hinj _ hN (homothety a) (homothety a) (hH a) g)

  have hTF : ∀ f : MvFormalGroup.CartierModule p Φ.F, p • f = 0 → f = 0 := by
    intro f hf
    apply hinj
    rw [map_zero]
    apply hTF₀
    rw [← map_nsmul, hf, map_zero]
  have hTFpow := pow_torsionFree (p := p) hTF
  have hTF₀pow := pow_torsionFree (p := p) hTF₀

  let T : MvFormalGroup.End Φ.F → MvFormalGroup.End Φ₀.F := fun e => ρ.comp (MvFormalGroup.Hom.comp e ρ')
  let T' : MvFormalGroup.End Φ₀.F → MvFormalGroup.End Φ.F := fun e₀ => ρ'.comp (MvFormalGroup.Hom.comp e₀ ρ)
  have mapT : ∀ e g, map (T e) g = θ (map e (θ' g)) := by
    intro e g
    dsimp only [T]
    rw [map_comp, map_comp, hρ', hρ]
  have mapT' : ∀ e₀ f, map (T' e₀) f = θ' (map e₀ (θ f)) := by
    intro e₀ f
    dsimp only [T']
    rw [map_comp, map_comp, hρ, hρ']

  have T_one : T 1 = ((p ^ N : ℕ) : MvFormalGroup.End Φ₀.F) := by
    refine hom_eq _ _ fun g => ?_
    rw [mapT, map_one_end, hθθ', map_natCast_end]
  have T_zero : T 0 = 0 := by
    refine hom_eq _ _ fun g => ?_
    rw [mapT, map_zero_end, map_zero, map_zero_end]
  have T_add : ∀ e e', T (e + e') = T e + T e' := by
    intro e e'
    refine hom_eq _ _ fun g => ?_
    rw [mapT, map_add_end, map_add, map_add_end, mapT, mapT]
  have T_mul : ∀ e e', T e * T e' = ((p ^ N : ℕ) : MvFormalGroup.End Φ₀.F) * T (e * e') := by
    intro e e'
    refine hom_eq _ _ fun g => ?_
    rw [map_mul_end, mapT, mapT, hθ'θ, map_nsmul, map_nsmul, map_mul_end, map_natCast_end, mapT,
      map_mul_end]
  have T'T_apply : ∀ e₀, T (T' e₀) =
      ((p ^ N : ℕ) : MvFormalGroup.End Φ₀.F) * (((p ^ N : ℕ) : MvFormalGroup.End Φ₀.F) * e₀) := by
    intro e₀
    refine hom_eq _ _ fun g => ?_
    rw [mapT, mapT', hθθ', hθθ', map_nsmul, map_mul_end, map_natCast_end, map_mul_end,
      map_natCast_end]

  have mem_S : ∀ {e : MvFormalGroup.End Φ.F},
      e ∈ Subring.centralizer (Set.range Φ.toFormalODModule.actEnd ∪ {Φ.toFormalODModule.varpiEnd}) ↔
      (∀ a, Φ.actEnd a * e = e * Φ.actEnd a) ∧ Φ.varpiEnd * e = e * Φ.varpiEnd := by
    intro e
    rw [Subring.mem_centralizer_iff]
    constructor
    · intro h
      exact ⟨fun a => h _ (Set.mem_union_left _ ⟨a, rfl⟩),
        h _ (Set.mem_union_right _ (Set.mem_singleton _))⟩
    · rintro ⟨h1, h2⟩ g hg
      rcases hg with ⟨a, rfl⟩ | hg
      · exact h1 a
      · rw [Set.mem_singleton_iff] at hg
        subst hg
        exact h2
  have mem_S₀ : ∀ {e : MvFormalGroup.End Φ₀.F},
      e ∈ Subring.centralizer (Set.range Φ₀.toFormalODModule.actEnd ∪ {Φ₀.toFormalODModule.varpiEnd}) ↔
      (∀ a, Φ₀.actEnd a * e = e * Φ₀.actEnd a) ∧ Φ₀.varpiEnd * e = e * Φ₀.varpiEnd := by
    intro e
    rw [Subring.mem_centralizer_iff]
    constructor
    · intro h
      exact ⟨fun a => h _ (Set.mem_union_left _ ⟨a, rfl⟩),
        h _ (Set.mem_union_right _ (Set.mem_singleton _))⟩
    · rintro ⟨h1, h2⟩ g hg
      rcases hg with ⟨a, rfl⟩ | hg
      · exact h1 a
      · rw [Set.mem_singleton_iff] at hg
        subst hg
        exact h2

  have T_mem : ∀ e, e ∈ Subring.centralizer (Set.range Φ.toFormalODModule.actEnd ∪ {Φ.toFormalODModule.varpiEnd}) →
      T e ∈ Subring.centralizer (Set.range Φ₀.toFormalODModule.actEnd ∪ {Φ₀.toFormalODModule.varpiEnd}) := by
    intro e he
    rw [mem_S] at he
    rw [mem_S₀]
    refine ⟨fun a => hom_eq _ _ fun g => ?_, hom_eq _ _ fun g => ?_⟩
    · rw [map_mul_end, mapT, ← endAct_apply, ← hAct, endAct_apply, ← map_mul_end, he.1 a,
        map_mul_end, ← endAct_apply (Φ.actEnd a), ← hAct', endAct_apply, map_mul_end, mapT]
    · rw [map_mul_end, mapT, ← endAct_apply, ← hPi, endAct_apply, ← map_mul_end, he.2,
        map_mul_end, ← endAct_apply Φ.varpiEnd, ← hPi', endAct_apply, map_mul_end, mapT]
  have T'_mem : ∀ e₀, e₀ ∈ Subring.centralizer (Set.range Φ₀.toFormalODModule.actEnd ∪ {Φ₀.toFormalODModule.varpiEnd}) →
      T' e₀ ∈ Subring.centralizer (Set.range Φ.toFormalODModule.actEnd ∪ {Φ.toFormalODModule.varpiEnd}) := by
    intro e₀ he
    rw [mem_S₀] at he
    rw [mem_S]
    refine ⟨fun a => hom_eq _ _ fun f => ?_, hom_eq _ _ fun f => ?_⟩
    · rw [map_mul_end, mapT', ← endAct_apply, ← hAct', endAct_apply, ← map_mul_end, he.1 a,
        map_mul_end, ← endAct_apply (Φ₀.actEnd a), ← hAct, endAct_apply, map_mul_end, mapT']
    · rw [map_mul_end, mapT', ← endAct_apply, ← hPi', endAct_apply, ← map_mul_end, he.2,
        map_mul_end, ← endAct_apply Φ₀.varpiEnd, ← hPi, endAct_apply, map_mul_end, mapT']

  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hpN0 : ((p : ℚ_[p]) ^ N) ≠ 0 := pow_ne_zero _ hp0
  set c : ℚ_[p] := ((p : ℚ_[p]) ^ N)⁻¹ with hc
  have hcpN : c * (p : ℚ_[p]) ^ N = 1 := inv_mul_cancel₀ hpN0
  let Tc : Subring.centralizer (Set.range Φ.toFormalODModule.actEnd ∪ {Φ.toFormalODModule.varpiEnd}) →
      Subring.centralizer (Set.range Φ₀.toFormalODModule.actEnd ∪ {Φ₀.toFormalODModule.varpiEnd}) := fun e => ⟨T e.1, T_mem e.1 e.2⟩
  have Tc_coe : ∀ e, (Tc e).1 = T e.1 := fun _ => rfl
  have castN : ∀ (X : Matrix (Fin 2) (Fin 2) ℚ_[p]),
      θ₀ (((p ^ N : ℕ) : Subring.centralizer (Set.range Φ₀.toFormalODModule.actEnd ∪ {Φ₀.toFormalODModule.varpiEnd}))) * X = (p : ℚ_[p]) ^ N • X := by
    intro X
    rw [map_natCast, natCast_mul_matrix, Nat.cast_pow]
  let θΦ : Subring.centralizer (Set.range Φ.toFormalODModule.actEnd ∪ {Φ.toFormalODModule.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[p] :=
    { toFun := fun e => c • θ₀ (Tc e)
      map_one' := by
        have h1 : Tc 1 = ((p ^ N : ℕ) : Subring.centralizer (Set.range Φ₀.toFormalODModule.actEnd ∪ {Φ₀.toFormalODModule.varpiEnd})) := by
          apply Subtype.ext
          rw [Tc_coe, Subring.coe_natCast]
          exact T_one
        show c • θ₀ (Tc 1) = 1
        rw [h1, ← mul_one (θ₀ _), castN, smul_smul, hcpN, one_smul]
      map_mul' := by
        intro e e'
        show c • θ₀ (Tc (e * e')) = c • θ₀ (Tc e) * c • θ₀ (Tc e')
        have hm : Tc e * Tc e' = ((p ^ N : ℕ) : Subring.centralizer (Set.range Φ₀.toFormalODModule.actEnd ∪ {Φ₀.toFormalODModule.varpiEnd})) * Tc (e * e') := by
          apply Subtype.ext
          show T e.1 * T e'.1 = ((p ^ N : ℕ) : MvFormalGroup.End Φ₀.F) * T (e.1 * e'.1)
          exact T_mul e.1 e'.1
        rw [smul_mul_smul_comm, ← map_mul, hm, map_mul, castN, smul_smul, mul_assoc, hcpN, mul_one]
      map_zero' := by
        have h0 : Tc 0 = 0 := by
          apply Subtype.ext
          show T 0 = 0
          exact T_zero
        show c • θ₀ (Tc 0) = 0
        rw [h0, map_zero, smul_zero]
      map_add' := by
        intro e e'
        show c • θ₀ (Tc (e + e')) = c • θ₀ (Tc e) + c • θ₀ (Tc e')
        have ha : Tc (e + e') = Tc e + Tc e' := by
          apply Subtype.ext
          show T (e.1 + e'.1) = T e.1 + T e'.1
          exact T_add e.1 e'.1
        rw [ha, map_add, smul_add] }
  have θΦ_apply : ∀ e, θΦ e = c • θ₀ (Tc e) := fun _ => rfl
  refine ⟨θΦ, ?_, N + m₀, ?_, ?_⟩
  ·
    intro e e' hee'
    rw [← sub_eq_zero] at hee' ⊢
    rw [← map_sub] at hee'
    set x := e - e' with hx
    rw [θΦ_apply, smul_eq_zero] at hee'
    rcases hee' with hc0 | hθ0
    · exact absurd hc0 (inv_ne_zero hpN0)
    · rw [← map_zero θ₀] at hθ0
      have hT0 : T x.1 = 0 := by
        have := congrArg Subtype.val (hθ₀ hθ0)
        simpa [Tc_coe] using this
      apply Subtype.ext
      show x.1 = 0
      refine hom_eq _ _ fun f => ?_
      rw [map_zero_end]
      apply hTFpow N
      have h1 : map (T x.1) (θ f) = 0 := by rw [hT0, map_zero_end]
      rw [mapT, hθ'θ, map_nsmul, ← map_zero θ] at h1
      exact hinj h1
  ·
    intro M
    obtain ⟨e₀, he₀⟩ := hS1 M
    refine ⟨⟨T' e₀.1, T'_mem e₀.1 e₀.2⟩, ?_⟩
    have hT : Tc ⟨T' e₀.1, T'_mem e₀.1 e₀.2⟩ =
        ((p ^ N : ℕ) : Subring.centralizer (Set.range Φ₀.toFormalODModule.actEnd ∪ {Φ₀.toFormalODModule.varpiEnd})) *
          (((p ^ N : ℕ) : Subring.centralizer (Set.range Φ₀.toFormalODModule.actEnd ∪ {Φ₀.toFormalODModule.varpiEnd})) * e₀) := by
      apply Subtype.ext
      show T (T' e₀.1) = ((p ^ N : ℕ) : MvFormalGroup.End Φ₀.F) *
        (((p ^ N : ℕ) : MvFormalGroup.End Φ₀.F) * e₀.1)
      exact T'T_apply e₀.1
    rw [θΦ_apply, hT, map_mul, map_mul, castN, castN, he₀, smul_smul, smul_smul, smul_smul, hcpN, one_mul,
      ← pow_add]
  ·
    intro e
    obtain ⟨M, hM⟩ := hS2 (Tc e)
    refine ⟨M, ?_⟩
    rw [θΦ_apply, smul_smul, pow_add, mul_assoc, mul_comm ((p : ℚ_[p]) ^ m₀) c, ← mul_assoc, mul_comm _ c,
      hcpN, one_mul, hM]

end P2mKcK2cAssembly

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (j : CerednikDrinfeld.Zp2 p →+* k) (Φ : CerednikDrinfeld.SpecialFormalODModule p j) :
    ∃ θ : Subring.centralizer
          (Set.range Φ.toFormalODModule.actEnd ∪ {Φ.toFormalODModule.varpiEnd}) →+*
        Matrix (Fin 2) (Fin 2) ℚ_[p],
      Function.Injective θ ∧
      ∃ m : ℕ,
        (∀ M : Matrix (Fin 2) (Fin 2) ℤ_[p],
          ∃ e, θ e = (p : ℚ_[p]) ^ m • M.map ((↑) : ℤ_[p] → ℚ_[p])) ∧
        (∀ e, ∃ M : Matrix (Fin 2) (Fin 2) ℤ_[p],
          (p : ℚ_[p]) ^ m • θ e = M.map ((↑) : ℤ_[p] → ℚ_[p])) :=
  P2mKcK2cAssembly.main j Φ

end

end S_CerednikDrinfeld_SpecialFormalODModule_exists_ringHom_centralizer_injective_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_ringHom_centralizer_injective_of_isAlgClosed (solution)
