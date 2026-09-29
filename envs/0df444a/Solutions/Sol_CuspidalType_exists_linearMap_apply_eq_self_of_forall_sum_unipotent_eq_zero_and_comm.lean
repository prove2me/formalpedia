-- Prove2me | solution 1 for CuspidalType.exists_linearMap_apply_eq_self_of_forall_sum_unipotent_eq_zero_and_comm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/bcc71aec-5c37-59b0-8494-61d69809ef95

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspidalType_exists_linearMap_apply_eq_self_of_forall_sum_unipotent_eq_zero_and_comm

set_option autoImplicit false

namespace CuspProjSol

open CuspidalType

variable {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem unipotent_mul (s t : ZMod q) : unipotent q s * unipotent q t = unipotent q (s + t) := by
  apply Units.ext
  rw [Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotent, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

variable (ρ : Representation K (GL2 q) V)

noncomputable def uniSum : V →ₗ[K] V := ∑ t : ZMod q, ρ (unipotent q t)

theorem uniSum_apply (v : V) : uniSum ρ v = ∑ t : ZMod q, ρ (unipotent q t) v := by
  simp [uniSum, LinearMap.sum_apply]

theorem rho_unipotent_uniSum (s : ZMod q) (v : V) :
    ρ (unipotent q s) (uniSum ρ v) = uniSum ρ v := by
  rw [uniSum_apply, map_sum]
  have h : ∀ t : ZMod q, ρ (unipotent q s) (ρ (unipotent q t) v) = ρ (unipotent q (s + t)) v := by
    intro t
    rw [← unipotent_mul, map_mul, Module.End.mul_apply]
  simp_rw [h]
  exact Fintype.sum_equiv (Equiv.addLeft s) _ _ (fun t => rfl)

theorem uniSum_uniSum (v : V) : uniSum ρ (uniSum ρ v) = (q : K) • uniSum ρ v := by
  rw [uniSum_apply ρ (uniSum ρ v)]
  simp_rw [rho_unipotent_uniSum]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, ← Nat.cast_smul_eq_nsmul K]

theorem sum_mul_apply (g : GL2 q) (v : V) :
    (∑ t : ZMod q, ρ (unipotent q t) * ρ g) v = uniSum ρ (ρ g v) := by
  rw [← Finset.sum_mul, Module.End.mul_apply]
  rfl

def cusp : Submodule K V where
  carrier := {v | ∀ g : GL2 q, uniSum ρ (ρ g v) = 0}
  zero_mem' := by
    intro g
    simp
  add_mem' := by
    intro a b ha hb g
    simp only [Set.mem_setOf_eq] at ha hb
    simp [map_add, ha g, hb g]
  smul_mem' := by
    intro c v hv g
    simp only [Set.mem_setOf_eq] at hv
    simp [map_smul, hv g]

theorem mem_cusp {v : V} : v ∈ cusp ρ ↔ ∀ g : GL2 q, uniSum ρ (ρ g v) = 0 := Iff.rfl

theorem cusp_stable (g : GL2 q) {v : V} (hv : v ∈ cusp ρ) : ρ g v ∈ cusp ρ := by
  intro h
  have h1 : ρ h (ρ g v) = ρ (h * g) v := by
    rw [map_mul, Module.End.mul_apply]
  rw [h1]
  exact hv (h * g)

def eisSet : Set V := {x | ∃ (g : GL2 q) (w : V), x = ρ g (uniSum ρ w)}

def eis : Submodule K V := Submodule.span K (eisSet ρ)

theorem uniSum_mem_eis (w : V) : uniSum ρ w ∈ eis ρ :=
  Submodule.subset_span ⟨1, w, by simp⟩

theorem rho_uniSum_mem_eis (g : GL2 q) (w : V) : ρ g (uniSum ρ w) ∈ eis ρ :=
  Submodule.subset_span ⟨g, w, rfl⟩

theorem eis_stable (g : GL2 q) {v : V} (hv : v ∈ eis ρ) : ρ g v ∈ eis ρ := by
  have hle : (eis ρ).map (ρ g) ≤ eis ρ := by
    rw [eis, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, ⟨h, w, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨g * h, w, ?_⟩
    rw [map_mul, Module.End.mul_apply]
  exact hle (Submodule.mem_map_of_mem hv)

def cuspSub : Subrepresentation ρ :=
  ⟨cusp ρ, fun g _ hv => cusp_stable ρ g hv⟩

def eisSub : Subrepresentation ρ :=
  ⟨eis ρ, fun g _ hv => eis_stable ρ g hv⟩

theorem uniSum_mem_sub (σ : Subrepresentation ρ) {v : V} (hv : v ∈ σ.toSubmodule) :
    uniSum ρ v ∈ σ.toSubmodule := by
  rw [uniSum_apply]
  exact Submodule.sum_mem _ (fun t _ => σ.apply_mem_toSubmodule _ hv)

theorem isCompl_toSubmodule {σ τ : Subrepresentation ρ} (h : IsCompl σ τ) :
    IsCompl σ.toSubmodule τ.toSubmodule := by
  constructor
  · rw [disjoint_iff]
    have h1 := h.disjoint
    rw [disjoint_iff] at h1
    exact congrArg Subrepresentation.toSubmodule h1
  · rw [codisjoint_iff]
    have h1 := h.codisjoint
    rw [codisjoint_iff] at h1
    exact congrArg Subrepresentation.toSubmodule h1

scoped instance instFiniteGL2 : Finite (GL2 q) := by
  unfold GL2 Matrix.GeneralLinearGroup
  infer_instance

theorem neZero_card [CharZero K] : NeZero (Nat.card (GL2 q) : K) := by
  refine ⟨?_⟩
  have h : 0 < Nat.card (GL2 q) := Nat.card_pos
  exact_mod_cast h.ne'

theorem isCompl_cusp_eis [CharZero K] : IsCompl (cusp ρ) (eis ρ) := by
  haveI := neZero_card (q := q) (K := K)
  have hqne : (q : K) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨U'', hU''⟩ := ComplementedLattice.exists_isCompl (cuspSub ρ ⊓ eisSub ρ)
    have hc : IsCompl (cusp ρ ⊓ eis ρ) U''.toSubmodule := isCompl_toSubmodule ρ hU''
    have h1 : ∀ w : V, uniSum ρ w ∈ U''.toSubmodule := by
      intro w
      have hmem : uniSum ρ w ∈ (cusp ρ ⊓ eis ρ) ⊔ U''.toSubmodule := by
        rw [hc.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
      have hNa : uniSum ρ a = 0 := by
        have := (Submodule.mem_inf.mp ha).1 1
        simpa using this
      have hq : (q : K) • uniSum ρ w = uniSum ρ b := by
        rw [← uniSum_uniSum, ← hab, map_add, hNa, zero_add]
      have hw : uniSum ρ w = (q : K)⁻¹ • uniSum ρ b := by
        rw [← hq, smul_smul, inv_mul_cancel₀ hqne, one_smul]
      rw [hw]
      exact Submodule.smul_mem _ _ (uniSum_mem_sub ρ U'' hb)
    have h2 : eis ρ ≤ U''.toSubmodule := by
      rw [eis]
      apply Submodule.span_le.mpr
      rintro _ ⟨g, w, rfl⟩
      exact U''.apply_mem_toSubmodule g (h1 w)
    have h3 := hc.disjoint
    rw [disjoint_iff] at h3 ⊢
    refine le_bot_iff.mp ?_
    calc cusp ρ ⊓ eis ρ = (cusp ρ ⊓ eis ρ) ⊓ eis ρ := by rw [inf_assoc, inf_idem]
      _ ≤ (cusp ρ ⊓ eis ρ) ⊓ U''.toSubmodule := inf_le_inf_left _ h2
      _ = ⊥ := h3
  ·
    obtain ⟨W, hW⟩ := ComplementedLattice.exists_isCompl (eisSub ρ)
    have hc : IsCompl (eis ρ) W.toSubmodule := isCompl_toSubmodule ρ hW
    have hWc : W.toSubmodule ≤ cusp ρ := by
      intro w hw g
      have h1 : uniSum ρ (ρ g w) ∈ W.toSubmodule := uniSum_mem_sub ρ W (W.apply_mem_toSubmodule g hw)
      have h2 : uniSum ρ (ρ g w) ∈ eis ρ := uniSum_mem_eis ρ _
      have h3 := hc.disjoint
      rw [disjoint_iff] at h3
      have h4 : uniSum ρ (ρ g w) ∈ eis ρ ⊓ W.toSubmodule := Submodule.mem_inf.mpr ⟨h2, h1⟩
      rw [h3] at h4
      exact (Submodule.mem_bot K).mp h4
    have h3 := hc.codisjoint
    rw [codisjoint_iff] at h3 ⊢
    refine top_le_iff.mp ?_
    calc (⊤ : Submodule K V) = eis ρ ⊔ W.toSubmodule := h3.symm
      _ ≤ eis ρ ⊔ cusp ρ := sup_le_sup_left hWc _
      _ = cusp ρ ⊔ eis ρ := sup_comm _ _

theorem exists_decomp [CharZero K] (v : V) :
    ∃ a b : V, a ∈ cusp ρ ∧ b ∈ eis ρ ∧ v = a + b := by
  have hmem : v ∈ cusp ρ ⊔ eis ρ := by
    rw [(isCompl_cusp_eis ρ).sup_eq_top]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
  exact ⟨a, b, ha, hb, hab.symm⟩

theorem proj_add [CharZero K] {a b : V} (ha : a ∈ cusp ρ) (hb : b ∈ eis ρ) :
    (cusp ρ).projection (eis ρ) (isCompl_cusp_eis ρ) (a + b) = a := by
  rw [map_add, Submodule.projection_apply_of_mem_right _ hb, add_zero]
  exact Submodule.projection_apply_left (isCompl_cusp_eis ρ) ⟨a, ha⟩

theorem comm_uniSum (T : V →ₗ[K] V) (hT : ∀ g : GL2 q, T ∘ₗ ρ g = ρ g ∘ₗ T) (v : V) :
    T (uniSum ρ v) = uniSum ρ (T v) := by
  rw [uniSum_apply, uniSum_apply, map_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  exact LinearMap.congr_fun (hT (unipotent q t)) v

theorem comm_cusp (T : V →ₗ[K] V) (hT : ∀ g : GL2 q, T ∘ₗ ρ g = ρ g ∘ₗ T) {v : V} (hv : v ∈ cusp ρ) :
    T v ∈ cusp ρ := by
  intro g
  have h1 : ρ g (T v) = T (ρ g v) := (LinearMap.congr_fun (hT g) v).symm
  rw [h1, ← comm_uniSum ρ T hT, hv g, map_zero]

theorem comm_eis (T : V →ₗ[K] V) (hT : ∀ g : GL2 q, T ∘ₗ ρ g = ρ g ∘ₗ T) {v : V} (hv : v ∈ eis ρ) :
    T v ∈ eis ρ := by
  have hle : (eis ρ).map T ≤ eis ρ := by
    rw [eis, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, ⟨h, w, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨h, T w, ?_⟩
    have h1 : T (ρ h (uniSum ρ w)) = ρ h (T (uniSum ρ w)) := LinearMap.congr_fun (hT h) _
    rw [h1, comm_uniSum ρ T hT]
  exact hle (Submodule.mem_map_of_mem hv)

theorem main [CharZero K]
    (Γ : Set (V →ₗ[K] V)) (hΓ : ∀ T ∈ Γ, ∀ g : CuspidalType.GL2 q, T ∘ₗ ρ g = ρ g ∘ₗ T) :
    ∃ eC : V →ₗ[K] V,
      (∀ v : V, (∀ g : CuspidalType.GL2 q, (∑ t : ZMod q, ρ (CuspidalType.unipotent q t) * ρ g) v = 0) →
        eC v = v) ∧
      (∀ g : CuspidalType.GL2 q, eC ∘ₗ ρ g = ρ g ∘ₗ eC) ∧
      (∀ T ∈ Γ, eC ∘ₗ T = T ∘ₗ eC) ∧
      (∀ (v : V) (g : CuspidalType.GL2 q),
        (∑ t : ZMod q, ρ (CuspidalType.unipotent q t) * ρ g) (eC v) = 0) := by
  have hc := isCompl_cusp_eis ρ
  refine ⟨(cusp ρ).projection (eis ρ) hc, ?_, ?_, ?_, ?_⟩
  · intro v hv
    have hv' : v ∈ cusp ρ := by
      intro g
      rw [← sum_mul_apply]
      exact hv g
    exact Submodule.projection_apply_left hc ⟨v, hv'⟩
  · intro g
    apply LinearMap.ext
    intro v
    obtain ⟨a, b, ha, hb, rfl⟩ := exists_decomp ρ v
    rw [LinearMap.comp_apply, LinearMap.comp_apply, map_add (ρ g), proj_add ρ ha hb,
      proj_add ρ (cusp_stable ρ g ha) (eis_stable ρ g hb)]
  · intro T hT
    apply LinearMap.ext
    intro v
    obtain ⟨a, b, ha, hb, rfl⟩ := exists_decomp ρ v
    rw [LinearMap.comp_apply, LinearMap.comp_apply, map_add T, proj_add ρ ha hb,
      proj_add ρ (comm_cusp ρ T (hΓ T hT) ha) (comm_eis ρ T (hΓ T hT) hb)]
  · intro v g
    rw [sum_mul_apply]
    have hmem : (cusp ρ).projection (eis ρ) hc v ∈ cusp ρ := Submodule.projection_apply_mem hc v
    exact hmem g

end CuspProjSol
p2m_reactivate "P2MW.S_CuspidalType_exists_linearMap_apply_eq_self_of_forall_sum_unipotent_eq_zero_and_comm.CuspProjSol"

theorem solution
    (q : ℕ) [Fact q.Prime] (K : Type*) [Field K] [CharZero K]
    (V : Type*) [AddCommGroup V] [Module K V]
    (ρ : Representation K (CuspidalType.GL2 q) V)
    (Γ : Set (V →ₗ[K] V)) (hΓ : ∀ T ∈ Γ, ∀ g : CuspidalType.GL2 q, T ∘ₗ ρ g = ρ g ∘ₗ T) :
    ∃ eC : V →ₗ[K] V,
      (∀ v : V, (∀ g : CuspidalType.GL2 q, (∑ t : ZMod q, ρ (CuspidalType.unipotent q t) * ρ g) v = 0) → eC v = v) ∧
      (∀ g : CuspidalType.GL2 q, eC ∘ₗ ρ g = ρ g ∘ₗ eC) ∧
      (∀ T ∈ Γ, eC ∘ₗ T = T ∘ₗ eC) ∧
      (∀ (v : V) (g : CuspidalType.GL2 q), (∑ t : ZMod q, ρ (CuspidalType.unipotent q t) * ρ g) (eC v) = 0) :=
  CuspProjSol.main ρ Γ hΓ

end S_CuspidalType_exists_linearMap_apply_eq_self_of_forall_sum_unipotent_eq_zero_and_comm
end P2MW
export P2MW.S_CuspidalType_exists_linearMap_apply_eq_self_of_forall_sum_unipotent_eq_zero_and_comm (solution)
