-- Prove2me | solution 1 for CuspForm.nonempty_basis_fin_one_gammaH_and_finrank_eigenspace_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/7061d832-89fc-519f-9c72-112cebff1c85

import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Order.SupIndep
import Theorems.Thm_CuspForm_exists_isPrimitiveForm_basis_gammaH_and_heckeTLinH_and_diamondLinH_and_heckeULinH_apply
import Theorems.Thm_Module_End_nonempty_basis_fin_one_and_finrank_iInf_eigenspace_eq_one_of_iSupIndep_of_cyclic
import Theorems.Thm_CuspForm_heckeULinH_comm
import Theorems.Thm_Module_End_mem_span_prod_apply_and_finrank_iInf_eigenspace_le_one_of_divisorString
import Theorems.Thm_Module_End_exists_mem_adjoin_apply_eq_self_and_apply_eq_zero_of_forall_ne_exists_ne
import Theorems.Thm_CuspForm_IsPrimitiveForm_level_eq_and_qCoeff_eq_of_forall_prime_notMem_qCoeff_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_nonempty_basis_fin_one_gammaH_and_finrank_eigenspace_eq_one
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 CuspForm.PeterssonCoset.mapGL_apply"

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open scoped MatrixGroups ModularForm
open Module

namespace M8T

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)

abbrev W : Type := CuspForm (CohCarrier.GammaH M H) 2

def Gf : Set (Module.End ℂ (W M H)) :=
  {T | (∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ℓ ∉ S ∧ T = CuspForm.heckeTLinH 2 hℓ hℓM) ∨
       (∃ q : ℕ, q.Prime ∧ q ∣ M ∧ T = CuspForm.heckeULinH 2 q) ∨
       (∃ d : (ZMod M)ˣ, T = CuspForm.diamondLinH 2 d)}

abbrev 𝔸 : Subalgebra ℂ (Module.End ℂ (W M H)) := Algebra.adjoin ℂ (Gf M H S)

structure Datum where
  n : ℕ
  L : Fin n → ℕ
  hL : ∀ i, L i ∣ M
  ε : (i : Fin n) → DirichletCharacter ℂ (L i)
  g : (i : Fin n) → CuspForm (CongruenceSubgroup.Gamma1 (L i)) 2
  G : Fin n → ℕ → W M H
  hprim : ∀ i, CuspForm.IsPrimitiveForm (ε i) (g i)
  hdist : ∀ i j, i ≠ j → L i ≠ L j ∨ ∃ m : ℕ, ModularFormClass.qCoeff (g i) m ≠ ModularFormClass.qCoeff (g j) m
  hεH : ∀ i, ∀ u : (ZMod M)ˣ, u ∈ H → DirichletCharacter.changeLevel (hL i) (ε i) (u : ZMod M) = 1
  hG : ∀ (i : Fin n) (d : ℕ), d ∣ M / L i →
    ∀ τ : UpperHalfPlane, G i d τ = g i (ModularForm.heckeDiagMatrix d • τ)
  hli : LinearIndependent ℂ (fun x : (Σ i : Fin n, ↥(Nat.divisors (M / L i))) => G x.1 (x.2 : ℕ))
  hspan : Submodule.span ℂ (Set.range fun x : (Σ i : Fin n, ↥(Nat.divisors (M / L i))) => G x.1 (x.2 : ℕ)) = ⊤
  hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (i : Fin n) (d : ℕ), d ∣ M / L i →
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    CuspForm.heckeTLinH 2 hℓ hℓM (G i d) = ModularFormClass.qCoeff (g i) ℓ • G i d
  hD : ∀ (u : (ZMod M)ˣ) (i : Fin n) (d : ℕ), d ∣ M / L i →
    CuspForm.diamondLinH 2 u (G i d) = DirichletCharacter.changeLevel (hL i) (ε i) (u : ZMod M) • G i d
  hU : ∀ (q : ℕ), q.Prime → q ∣ M → ∀ (i : Fin n) (d : ℕ), d ∣ M / L i →
    (q ∣ d → CuspForm.heckeULinH 2 q (G i d) = G i (d / q)) ∧
    (¬ q ∣ d → q ∣ L i → CuspForm.heckeULinH 2 q (G i d) = ModularFormClass.qCoeff (g i) q • G i d) ∧
    (¬ q ∣ d → ¬ q ∣ L i → CuspForm.heckeULinH 2 q (G i d) =
      ModularFormClass.qCoeff (g i) q • G i d - (ε i (q : ZMod (L i)) * (q : ℂ) ^ ((2 : ℤ) - 1)) • G i (d * q))

theorem nonempty_datum : Nonempty (Datum M H) := by
  obtain ⟨n, L, hL, ε, g, G, hprim, hdist, hεH, hG, hli, hspan, hT, hD, hU⟩ :=
    CuspForm.exists_isPrimitiveForm_basis_gammaH_and_heckeTLinH_and_diamondLinH_and_heckeULinH_apply M H 2
  exact ⟨⟨n, L, hL, ε, g, G, hprim, hdist, hεH, hG, hli, hspan, hT, hD, hU⟩⟩

variable {M H}
variable (𝒟 : Datum M H)

abbrev Idx : Type := Σ i : Fin 𝒟.n, ↥(Nat.divisors (M / 𝒟.L i))

def vec (x : Idx 𝒟) : W M H := 𝒟.G x.1 (x.2 : ℕ)

def basis : Module.Basis (Idx 𝒟) ℂ (W M H) :=
  Module.Basis.mk (v := vec 𝒟) 𝒟.hli (by
    have : Set.range (vec 𝒟) = Set.range fun x : Idx 𝒟 => 𝒟.G x.1 (x.2 : ℕ) := rfl
    rw [this, 𝒟.hspan])

theorem basis_apply (x : Idx 𝒟) : basis 𝒟 x = 𝒟.G x.1 (x.2 : ℕ) := by
  simp [basis, vec]

include 𝒟 in
theorem finiteDimensional : FiniteDimensional ℂ (W M H) :=
  Module.Basis.finiteDimensional_of_finite (basis 𝒟)

def V (i : Fin 𝒟.n) : Submodule ℂ (W M H) :=
  Submodule.span ℂ (Set.range fun d : ↥(Nat.divisors (M / 𝒟.L i)) => 𝒟.G i (d : ℕ))

theorem G_mem_V (i : Fin 𝒟.n) {d : ℕ} (hd : d ∣ M / 𝒟.L i) : 𝒟.G i d ∈ V 𝒟 i := by
  have hD : M / 𝒟.L i ≠ 0 := by
    have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) (𝒟.hL i))
      (Nat.pos_of_ne_zero (fun h => by have := 𝒟.hL i; rw [h, zero_dvd_iff] at this; exact NeZero.ne M this))
    omega
  exact Submodule.subset_span ⟨⟨d, Nat.mem_divisors.mpr ⟨hd, hD⟩⟩, rfl⟩

theorem range_vec_image (i : Fin 𝒟.n) :
    vec 𝒟 '' (Sigma.fst ⁻¹' {i}) = Set.range fun d : ↥(Nat.divisors (M / 𝒟.L i)) => 𝒟.G i (d : ℕ) := by
  ext w
  simp only [Set.mem_image, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_range, vec]
  constructor
  · rintro ⟨⟨j, d⟩, rfl, rfl⟩; exact ⟨d, rfl⟩
  · rintro ⟨d, rfl⟩; exact ⟨⟨i, d⟩, rfl, rfl⟩

theorem V_eq_span_image (i : Fin 𝒟.n) : V 𝒟 i = Submodule.span ℂ (vec 𝒟 '' (Sigma.fst ⁻¹' {i})) := by
  rw [range_vec_image]; rfl

theorem V_iSupIndep : iSupIndep (V 𝒟) := by
  classical
  intro i
  have hdis : Disjoint ((Sigma.fst : Idx 𝒟 → Fin 𝒟.n) ⁻¹' ({i} : Set (Fin 𝒟.n)))
      ((Sigma.fst : Idx 𝒟 → Fin 𝒟.n) ⁻¹' ({i}ᶜ : Set (Fin 𝒟.n))) :=
    Disjoint.preimage _ disjoint_compl_right
  have key : Disjoint (Submodule.span ℂ (vec 𝒟 '' (Sigma.fst ⁻¹' {i})))
      (Submodule.span ℂ (vec 𝒟 '' (Sigma.fst ⁻¹' {i}ᶜ))) := 𝒟.hli.disjoint_span_image hdis
  rw [V_eq_span_image]
  refine key.mono_right ?_
  refine iSup₂_le fun j hj => ?_
  rw [V_eq_span_image]
  apply Submodule.span_mono
  apply Set.image_mono
  intro x hx
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
  simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff, hx]
  exact hj

theorem V_iSup_eq_top : iSup (V 𝒟) = ⊤ := by
  apply top_unique
  rw [← 𝒟.hspan, Submodule.span_le]
  rintro _ ⟨⟨i, d⟩, rfl⟩
  exact Submodule.mem_iSup_of_mem i (G_mem_V 𝒟 i (Nat.dvd_of_mem_divisors d.2))

theorem scalar_on_V (T : Module.End ℂ (W M H)) (i : Fin 𝒟.n) (c : ℂ)
    (h : ∀ d : ℕ, d ∣ M / 𝒟.L i → T (𝒟.G i d) = c • 𝒟.G i d) : ∀ v ∈ V 𝒟 i, T v = c • v := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨d, rfl⟩ := hx; exact h d (Nat.dvd_of_mem_divisors d.2)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul a x _ hx => rw [map_smul, hx, smul_comm]

theorem stab_on_V (T : Module.End ℂ (W M H)) (i : Fin 𝒟.n)
    (h : ∀ d : ℕ, d ∣ M / 𝒟.L i → T (𝒟.G i d) ∈ V 𝒟 i) : ∀ v ∈ V 𝒟 i, T v ∈ V 𝒟 i := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨d, rfl⟩ := hx; exact h d (Nat.dvd_of_mem_divisors d.2)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

end M8T

namespace M8T

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} (S : Set ℕ) (𝒟 : Datum M H)

open ModularFormClass

theorem heckeT_scalar {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (i : Fin 𝒟.n) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ∀ v ∈ V 𝒟 i, CuspForm.heckeTLinH 2 hℓ hℓM v = qCoeff (𝒟.g i) ℓ • v :=
  scalar_on_V 𝒟 _ i _ (fun d hd => 𝒟.hT ℓ hℓ hℓM i d hd)

theorem diamond_scalar (u : (ZMod M)ˣ) (i : Fin 𝒟.n) :
    ∀ v ∈ V 𝒟 i, CuspForm.diamondLinH 2 u v = DirichletCharacter.changeLevel (𝒟.hL i) (𝒟.ε i) (u : ZMod M) • v :=
  scalar_on_V 𝒟 _ i _ (fun d hd => 𝒟.hD u i d hd)

theorem L_ne_zero (i : Fin 𝒟.n) : 𝒟.L i ≠ 0 := fun h => by
  have := 𝒟.hL i; rw [h, zero_dvd_iff] at this; exact NeZero.ne M this

theorem mul_dvd_div {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (i : Fin 𝒟.n) (hqL : ¬ q ∣ 𝒟.L i) {d : ℕ}
    (hd : d ∣ M / 𝒟.L i) (hqd : ¬ q ∣ d) : d * q ∣ M / 𝒟.L i := by
  have hcop : Nat.Coprime d q := Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqd)
  refine hcop.mul_dvd_of_dvd_of_dvd hd ?_
  have hqML : Nat.Coprime q (𝒟.L i) := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqL
  have : q ∣ 𝒟.L i * (M / 𝒟.L i) := by rw [Nat.mul_div_cancel' (𝒟.hL i)]; exact hqM
  exact hqML.dvd_of_dvd_mul_left this

theorem heckeU_G_mem {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (i : Fin 𝒟.n) {d : ℕ} (hd : d ∣ M / 𝒟.L i) :
    CuspForm.heckeULinH 2 q (𝒟.G i d) ∈ V 𝒟 i := by
  obtain ⟨h1, h2, h3⟩ := 𝒟.hU q hq hqM i d hd
  by_cases hqd : q ∣ d
  · rw [h1 hqd]; exact G_mem_V 𝒟 i ((Nat.div_dvd_of_dvd hqd).trans hd)
  · by_cases hqL : q ∣ 𝒟.L i
    · rw [h2 hqd hqL]; exact Submodule.smul_mem _ _ (G_mem_V 𝒟 i hd)
    · rw [h3 hqd hqL]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (G_mem_V 𝒟 i hd))
        (Submodule.smul_mem _ _ (G_mem_V 𝒟 i (mul_dvd_div 𝒟 hq hqM i hqL hd hqd)))

theorem heckeU_stab {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (i : Fin 𝒟.n) :
    ∀ v ∈ V 𝒟 i, CuspForm.heckeULinH 2 q v ∈ V 𝒟 i :=
  stab_on_V 𝒟 _ i (fun _ hd => heckeU_G_mem 𝒟 hq hqM i hd)

theorem gen_stab : ∀ T ∈ Gf M H S, ∀ (i : Fin 𝒟.n), ∀ v ∈ V 𝒟 i, T v ∈ V 𝒟 i := by
  rintro T (⟨ℓ, hℓ, hℓM, -, rfl⟩ | ⟨q, hq, hqM, rfl⟩ | ⟨u, rfl⟩) i v hv
  · rw [heckeT_scalar 𝒟 hℓ hℓM i v hv]; exact Submodule.smul_mem _ _ hv
  · exact heckeU_stab 𝒟 hq hqM i v hv
  · rw [diamond_scalar 𝒟 u i v hv]; exact Submodule.smul_mem _ _ hv

theorem A_stab : ∀ a ∈ 𝔸 M H S, ∀ (i : Fin 𝒟.n), ∀ v ∈ V 𝒟 i, a v ∈ V 𝒟 i := by
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact gen_stab S 𝒟 x hx
  | algebraMap r => intro i v hv; rw [Module.algebraMap_end_apply]; exact Submodule.smul_mem _ _ hv
  | add x y _ _ hx hy => intro i v hv; rw [LinearMap.add_apply]; exact Submodule.add_mem _ (hx i v hv) (hy i v hv)
  | mul x y _ _ hx hy => intro i v hv; rw [Module.End.mul_apply]; exact hx i _ (hy i v hv)

theorem comm_of_scalar_of_stab (A B : Module.End ℂ (W M H)) (c : Fin 𝒟.n → ℂ)
    (hA : ∀ (i : Fin 𝒟.n), ∀ v ∈ V 𝒟 i, A v = c i • v) (hB : ∀ (i : Fin 𝒟.n), ∀ v ∈ V 𝒟 i, B v ∈ V 𝒟 i) :
    A * B = B * A := by
  refine (basis 𝒟).ext fun x => ?_
  obtain ⟨i, d⟩ := x
  have hmem : 𝒟.G i d ∈ V 𝒟 i := G_mem_V 𝒟 i (Nat.dvd_of_mem_divisors d.2)
  rw [basis_apply, Module.End.mul_apply, Module.End.mul_apply, hA i _ (hB i _ hmem), hA i _ hmem, map_smul]

include 𝒟 in
theorem gen_comm : ∀ A ∈ Gf M H S, ∀ B ∈ Gf M H S, Commute A B := by
  intro A hA B hB
  have hBstab := gen_stab S 𝒟 B hB
  have hAstab := gen_stab S 𝒟 A hA
  rcases hA with ⟨ℓ, hℓ, hℓM, -, rfl⟩ | ⟨q, hq, hqM, rfl⟩ | ⟨u, rfl⟩
  · exact comm_of_scalar_of_stab 𝒟 _ _ _ (fun i => heckeT_scalar 𝒟 hℓ hℓM i) hBstab
  · rcases hB with ⟨ℓ, hℓ, hℓM, -, rfl⟩ | ⟨q', hq', hq'M, rfl⟩ | ⟨u, rfl⟩
    · exact (comm_of_scalar_of_stab 𝒟 _ _ _ (fun i => heckeT_scalar 𝒟 hℓ hℓM i) hAstab).symm
    · exact LinearMap.ext fun f => (CuspForm.heckeULinH_comm M H 2 hq' hq'M hq hqM f).symm
    · exact (comm_of_scalar_of_stab 𝒟 _ _ _ (fun i => diamond_scalar 𝒟 u i) hAstab).symm
  · exact comm_of_scalar_of_stab 𝒟 _ _ _ (fun i => diamond_scalar 𝒟 u i) hBstab

include 𝒟 in
theorem A_comm : ∀ a ∈ 𝔸 M H S, ∀ b ∈ 𝔸 M H S, a * b = b * a := by
  intro a ha b hb
  have h1 : ∀ x ∈ Gf M H S, Commute x b := fun x hx =>
    Algebra.commute_of_mem_adjoin_of_forall_mem_commute hb (fun y hy => gen_comm S 𝒟 x hx y hy)
  exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha (fun x hx => (h1 x hx).symm)).symm.eq

def Tset : Set (Module.End ℂ (W M H)) :=
  {T | (∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ℓ ∉ S ∧ T = CuspForm.heckeTLinH 2 hℓ hℓM) ∨
       (∃ d : (ZMod M)ˣ, T = CuspForm.diamondLinH 2 d)}

theorem Tset_subset : Tset (M := M) (H := H) S ⊆ Gf M H S := by
  rintro T (h | h)
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

theorem div_mem_divisors (i : Fin 𝒟.n) : M / 𝒟.L i ∈ Nat.divisors (M / 𝒟.L i) := by
  refine Nat.mem_divisors_self _ ?_
  have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) (𝒟.hL i))
    (Nat.pos_of_ne_zero (fun h => by have := 𝒟.hL i; rw [h, zero_dvd_iff] at this; exact NeZero.ne M this))
  omega

def top (i : Fin 𝒟.n) : Idx 𝒟 := ⟨i, ⟨M / 𝒟.L i, div_mem_divisors 𝒟 i⟩⟩

def csc (T : Module.End ℂ (W M H)) (i : Fin 𝒟.n) : ℂ :=
  (basis 𝒟).repr (T (𝒟.G i (M / 𝒟.L i))) (top 𝒟 i)

theorem csc_eq_of_scalar (T : Module.End ℂ (W M H)) (i : Fin 𝒟.n) (c : ℂ)
    (h : ∀ v ∈ V 𝒟 i, T v = c • v) : csc 𝒟 T i = c := by
  unfold csc
  rw [h _ (G_mem_V 𝒟 i dvd_rfl), show 𝒟.G i (M / 𝒟.L i) = basis 𝒟 (top 𝒟 i) by rw [basis_apply]; rfl,
    map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]

theorem Tset_scalar : ∀ T ∈ Tset (M := M) (H := H) S, ∀ (i : Fin 𝒟.n), ∀ v ∈ V 𝒟 i, T v = csc 𝒟 T i • v := by
  rintro T (⟨ℓ, hℓ, hℓM, -, rfl⟩ | ⟨u, rfl⟩) i v hv
  · rw [csc_eq_of_scalar 𝒟 _ i _ (heckeT_scalar 𝒟 hℓ hℓM i), heckeT_scalar 𝒟 hℓ hℓM i v hv]
  · rw [csc_eq_of_scalar 𝒟 _ i _ (diamond_scalar 𝒟 u i), diamond_scalar 𝒟 u i v hv]

theorem Tset_sep (hSfin : S.Finite) :
    ∀ i j : Fin 𝒟.n, i ≠ j → ∃ T ∈ Tset (M := M) (H := H) S, csc 𝒟 T i ≠ csc 𝒟 T j := by
  classical
  intro i j hij
  by_cases hχ : DirichletCharacter.changeLevel (𝒟.hL i) (𝒟.ε i) = DirichletCharacter.changeLevel (𝒟.hL j) (𝒟.ε j)
  · by_contra hall
    push Not at hall
    have ha : ∀ p : ℕ, p.Prime → p ∉ hSfin.toFinset ∪ M.primeFactors →
        qCoeff (𝒟.g i) p = qCoeff (𝒟.g j) p := by
      intro p hp hpS
      have hpM : ¬ p ∣ M := fun h =>
        hpS (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp, h, NeZero.ne M⟩))
      have hpS' : p ∉ S := fun h => hpS (Finset.mem_union_left _ (hSfin.mem_toFinset.mpr h))
      have := hall _ (Or.inl ⟨p, hp, hpM, hpS', rfl⟩)
      rwa [csc_eq_of_scalar 𝒟 _ i _ (heckeT_scalar 𝒟 hp hpM i),
        csc_eq_of_scalar 𝒟 _ j _ (heckeT_scalar 𝒟 hp hpM j)] at this
    have hε : ∀ p : ℕ, p.Prime → p ∉ hSfin.toFinset ∪ M.primeFactors →
        𝒟.ε i (p : ZMod (𝒟.L i)) = 𝒟.ε j (p : ZMod (𝒟.L j)) := by
      intro p hp hpS
      have hpM : ¬ p ∣ M := fun h =>
        hpS (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp, h, NeZero.ne M⟩))
      have hu : IsUnit (p : ZMod M) := (ZMod.isUnit_prime_iff_not_dvd hp).mpr hpM
      have := congrArg (fun χ : DirichletCharacter ℂ M => χ (hu.unit : ZMod M)) hχ
      rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd,
        IsUnit.unit_spec, ZMod.cast_natCast (𝒟.hL i), ZMod.cast_natCast (𝒟.hL j)] at this
      exact this
    haveI : NeZero (𝒟.L i) := ⟨L_ne_zero 𝒟 i⟩
    haveI : NeZero (𝒟.L j) := ⟨L_ne_zero 𝒟 j⟩
    have key := CuspForm.IsPrimitiveForm.level_eq_and_qCoeff_eq_of_forall_prime_notMem_qCoeff_eq
      (𝒟.hprim i) (𝒟.hprim j) (hSfin.toFinset ∪ M.primeFactors) ha hε
    rcases 𝒟.hdist i j hij with h | ⟨m, hm⟩
    · exact h key.1
    · exact hm (key.2 m)
  · have : ∃ u : (ZMod M)ˣ, DirichletCharacter.changeLevel (𝒟.hL i) (𝒟.ε i) (u : ZMod M) ≠
        DirichletCharacter.changeLevel (𝒟.hL j) (𝒟.ε j) (u : ZMod M) := by
      by_contra h
      push Not at h
      exact hχ (MulChar.ext h)
    obtain ⟨u, hu⟩ := this
    refine ⟨CuspForm.diamondLinH 2 u, Or.inr ⟨u, rfl⟩, ?_⟩
    rwa [csc_eq_of_scalar 𝒟 _ i _ (diamond_scalar 𝒟 u i), csc_eq_of_scalar 𝒟 _ j _ (diamond_scalar 𝒟 u j)]

theorem exists_idempotents (hSfin : S.Finite) (i : Fin 𝒟.n) :
    ∃ e ∈ 𝔸 M H S, (∀ v ∈ V 𝒟 i, e v = v) ∧ ∀ j : Fin 𝒟.n, j ≠ i → ∀ v ∈ V 𝒟 j, e v = 0 := by
  classical
  obtain ⟨e, he, h1, h2⟩ :=
    Module.End.exists_mem_adjoin_apply_eq_self_and_apply_eq_zero_of_forall_ne_exists_ne
      (V 𝒟) (Tset (M := M) (H := H) S) (csc 𝒟) (Tset_scalar S 𝒟) (Tset_sep S 𝒟 hSfin) i
  exact ⟨e, Algebra.adjoin_mono (Tset_subset S) he, h1, h2⟩

end M8T

namespace M8T

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} (S : Set ℕ) (𝒟 : Datum M H)

open ModularFormClass

section oneClass

variable (i : Fin 𝒟.n)

abbrev Dtop : ℕ := M / 𝒟.L i

theorem Dtop_ne_zero : Dtop 𝒟 i ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors (div_mem_divisors 𝒟 i))

theorem Dtop_dvd : Dtop 𝒟 i ∣ M := Nat.div_dvd_of_dvd (𝒟.hL i)

def ev (d : ℕ) : ↥(V 𝒟 i) :=
  if h : d ∣ Dtop 𝒟 i then ⟨𝒟.G i d, G_mem_V 𝒟 i h⟩ else 0

theorem ev_of_dvd {d : ℕ} (h : d ∣ Dtop 𝒟 i) : ev 𝒟 i d = ⟨𝒟.G i d, G_mem_V 𝒟 i h⟩ := dif_pos h

theorem coe_ev_of_dvd {d : ℕ} (h : d ∣ Dtop 𝒟 i) : (ev 𝒟 i d : W M H) = 𝒟.G i d := by
  rw [ev_of_dvd 𝒟 i h]

def Ur (q : ℕ) : Module.End ℂ ↥(V 𝒟 i) :=
  if h : q.Prime ∧ q ∣ M then (CuspForm.heckeULinH 2 q).restrict (heckeU_stab 𝒟 h.1 h.2 i) else 0

theorem Ur_of (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) :
    Ur 𝒟 i q = (CuspForm.heckeULinH 2 q).restrict (heckeU_stab 𝒟 hq hqM i) := dif_pos ⟨hq, hqM⟩

theorem coe_Ur_apply {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (x : ↥(V 𝒟 i)) :
    (Ur 𝒟 i q x : W M H) = CuspForm.heckeULinH 2 q (x : W M H) := by
  rw [Ur_of 𝒟 i q hq hqM, LinearMap.restrict_apply]

theorem ev_linearIndependent :
    LinearIndependent ℂ (fun d : ↥(Nat.divisors (Dtop 𝒟 i)) => ev 𝒟 i (d : ℕ)) := by
  apply LinearIndependent.of_comp (V 𝒟 i).subtype
  have : (V 𝒟 i).subtype ∘ (fun d : ↥(Nat.divisors (Dtop 𝒟 i)) => ev 𝒟 i (d : ℕ)) =
      (fun x : Idx 𝒟 => 𝒟.G x.1 (x.2 : ℕ)) ∘ (Sigma.mk i) := by
    funext d
    simp only [Function.comp_apply, Submodule.subtype_apply]
    exact coe_ev_of_dvd 𝒟 i (Nat.dvd_of_mem_divisors d.2)
  rw [this]
  exact 𝒟.hli.comp _ sigma_mk_injective

theorem ev_span :
    Submodule.span ℂ (Set.range fun d : ↥(Nat.divisors (Dtop 𝒟 i)) => ev 𝒟 i (d : ℕ)) = ⊤ := by
  apply Submodule.map_injective_of_injective (V 𝒟 i).injective_subtype
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
  have : ⇑(V 𝒟 i).subtype ∘ (fun d : ↥(Nat.divisors (Dtop 𝒟 i)) => ev 𝒟 i (d : ℕ)) =
      fun d : ↥(Nat.divisors (M / 𝒟.L i)) => 𝒟.G i (d : ℕ) := by
    funext d
    simp only [Function.comp_apply, Submodule.subtype_apply]
    exact coe_ev_of_dvd 𝒟 i (Nat.dvd_of_mem_divisors d.2)
  rw [this]; rfl

theorem Ur_comm : ∀ p q : ℕ, p.Prime → q.Prime → p ∣ Dtop 𝒟 i → q ∣ Dtop 𝒟 i →
    Commute (Ur 𝒟 i p) (Ur 𝒟 i q) := by
  intro p q hp hq hpD hqD
  have hpM := hpD.trans (Dtop_dvd 𝒟 i)
  have hqM := hqD.trans (Dtop_dvd 𝒟 i)
  refine LinearMap.ext fun x => Subtype.ext ?_
  change ((Ur 𝒟 i p) ((Ur 𝒟 i q) x) : W M H) = ((Ur 𝒟 i q) ((Ur 𝒟 i p) x) : W M H)
  rw [coe_Ur_apply 𝒟 i hp hpM, coe_Ur_apply 𝒟 i hq hqM, coe_Ur_apply 𝒟 i hq hqM, coe_Ur_apply 𝒟 i hp hpM]
  exact CuspForm.heckeULinH_comm M H 2 hp hpM hq hqM _

theorem Ur_down : ∀ q : ℕ, q.Prime → q ∣ Dtop 𝒟 i → ∀ d : ℕ, d ∣ Dtop 𝒟 i → q ∣ d →
    Ur 𝒟 i q (ev 𝒟 i d) = ev 𝒟 i (d / q) := by
  intro q hq hqD d hd hqd
  have hqM := hqD.trans (Dtop_dvd 𝒟 i)
  apply Subtype.ext
  rw [coe_Ur_apply 𝒟 i hq hqM, coe_ev_of_dvd 𝒟 i hd, coe_ev_of_dvd 𝒟 i ((Nat.div_dvd_of_dvd hqd).trans hd)]
  exact (𝒟.hU q hq hqM i d hd).1 hqd

theorem Ur_base : ∀ q : ℕ, q.Prime → q ∣ Dtop 𝒟 i → ∃ a b : ℂ, ∀ d : ℕ, d ∣ Dtop 𝒟 i → ¬ q ∣ d →
    Ur 𝒟 i q (ev 𝒟 i d) = a • ev 𝒟 i d + b • ev 𝒟 i (d * q) := by
  intro q hq hqD
  have hqM := hqD.trans (Dtop_dvd 𝒟 i)
  by_cases hqL : q ∣ 𝒟.L i
  · refine ⟨qCoeff (𝒟.g i) q, 0, fun d hd hqd => ?_⟩
    rw [zero_smul, add_zero]
    apply Subtype.ext
    rw [coe_Ur_apply 𝒟 i hq hqM, Submodule.coe_smul, coe_ev_of_dvd 𝒟 i hd]
    exact (𝒟.hU q hq hqM i d hd).2.1 hqd hqL
  · refine ⟨qCoeff (𝒟.g i) q, -(𝒟.ε i (q : ZMod (𝒟.L i)) * (q : ℂ) ^ ((2 : ℤ) - 1)), fun d hd hqd => ?_⟩
    apply Subtype.ext
    rw [coe_Ur_apply 𝒟 i hq hqM, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul,
      coe_ev_of_dvd 𝒟 i hd, coe_ev_of_dvd 𝒟 i (mul_dvd_div 𝒟 hq hqM i hqL hd hqd), neg_smul,
      ← sub_eq_add_neg]
    exact (𝒟.hU q hq hqM i d hd).2.2 hqd hqL

theorem string :
    (∀ d : ℕ, d ∣ Dtop 𝒟 i → ∃ T ∈ Algebra.adjoin ℂ {A : Module.End ℂ ↥(V 𝒟 i) |
        ∃ q : ℕ, q.Prime ∧ q ∣ Dtop 𝒟 i ∧ A = Ur 𝒟 i q}, ev 𝒟 i d = T (ev 𝒟 i (Dtop 𝒟 i))) ∧
    ∀ lam : ℕ → ℂ, Module.finrank ℂ
      ↥(⨅ q ∈ (Dtop 𝒟 i).primeFactors, Module.End.eigenspace (Ur 𝒟 i q) (lam q)) ≤ 1 := by
  haveI := finiteDimensional 𝒟
  exact Module.End.mem_span_prod_apply_and_finrank_iInf_eigenspace_le_one_of_divisorString
    (Dtop 𝒟 i) (Dtop_ne_zero 𝒟 i) ↥(V 𝒟 i) (ev 𝒟 i) (ev_linearIndependent 𝒟 i) (ev_span 𝒟 i)
    (Ur 𝒟 i) (Ur_comm 𝒟 i) (Ur_down 𝒟 i) (Ur_base 𝒟 i)

theorem lift {T : Module.End ℂ ↥(V 𝒟 i)}
    (hT : T ∈ Algebra.adjoin ℂ {A : Module.End ℂ ↥(V 𝒟 i) | ∃ q : ℕ, q.Prime ∧ q ∣ Dtop 𝒟 i ∧ A = Ur 𝒟 i q}) :
    ∃ a ∈ 𝔸 M H S, ∀ x : ↥(V 𝒟 i), (T x : W M H) = a (x : W M H) := by
  induction hT using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨q, hq, hqD, rfl⟩ := hx
    have hqM := hqD.trans (Dtop_dvd 𝒟 i)
    exact ⟨CuspForm.heckeULinH 2 q, Algebra.subset_adjoin (Or.inr (Or.inl ⟨q, hq, hqM, rfl⟩)),
      fun x => coe_Ur_apply 𝒟 i hq hqM x⟩
  | algebraMap r =>
    exact ⟨algebraMap ℂ _ r, Subalgebra.algebraMap_mem _ r, fun x => by
      rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, Submodule.coe_smul]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hbx⟩ := hy
    exact ⟨a + b, Subalgebra.add_mem _ ha hb, fun v => by
      rw [LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, hax, hbx]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hbx⟩ := hy
    exact ⟨a * b, Subalgebra.mul_mem _ ha hb, fun v => by
      rw [Module.End.mul_apply, Module.End.mul_apply, hax, hbx]⟩

theorem cyclic : ∀ v ∈ V 𝒟 i, ∃ a : ↥(𝔸 M H S), (a : Module.End ℂ (W M H)) (𝒟.G i (M / 𝒟.L i)) = v := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d, rfl⟩ := hx
    have hd : (d : ℕ) ∣ Dtop 𝒟 i := Nat.dvd_of_mem_divisors d.2
    obtain ⟨T, hT, hTe⟩ := (string 𝒟 i).1 d hd
    obtain ⟨a, ha, hax⟩ := lift S 𝒟 i hT
    refine ⟨⟨a, ha⟩, ?_⟩
    have := congrArg (fun x : ↥(V 𝒟 i) => (x : W M H)) hTe
    rw [coe_ev_of_dvd 𝒟 i hd, hax, coe_ev_of_dvd 𝒟 i dvd_rfl] at this
    exact this.symm
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [Subalgebra.coe_add, LinearMap.add_apply, ha, hb]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c • a, by rw [Subalgebra.coe_smul, LinearMap.smul_apply, ha]⟩

theorem eigen_le_one (χ : ↥(𝔸 M H S) →ₐ[ℂ] ℂ) :
    Module.finrank ℂ ↥(V 𝒟 i ⊓ ⨅ a : ↥(𝔸 M H S),
      Module.End.eigenspace (a : Module.End ℂ (W M H)) (χ a)) ≤ 1 := by
  classical
  haveI := finiteDimensional 𝒟
  set X := V 𝒟 i ⊓ ⨅ a : ↥(𝔸 M H S), Module.End.eigenspace (a : Module.End ℂ (W M H)) (χ a) with hX
  let lam : ℕ → ℂ := fun q =>
    if h : q.Prime ∧ q ∣ M then
      χ ⟨CuspForm.heckeULinH 2 q, Algebra.subset_adjoin (Or.inr (Or.inl ⟨q, h.1, h.2, rfl⟩))⟩
    else 0
  set Y := ⨅ q ∈ (Dtop 𝒟 i).primeFactors, Module.End.eigenspace (Ur 𝒟 i q) (lam q) with hY
  have hle := (string 𝒟 i).2 lam
  let φ : ↥X →ₗ[ℂ] ↥(V 𝒟 i) := Submodule.inclusion inf_le_left
  have hφ : Function.Injective φ := Submodule.inclusion_injective _
  have hrange : LinearMap.range φ ≤ Y := by
    rintro _ ⟨x, rfl⟩
    rw [hY, Submodule.mem_iInf]
    intro q
    rw [Submodule.mem_iInf]
    intro hq
    have hq' := Nat.mem_primeFactors.mp hq
    have hqM : q ∣ M := hq'.2.1.trans (Dtop_dvd 𝒟 i)
    rw [Module.End.mem_eigenspace_iff]
    apply Subtype.ext
    rw [coe_Ur_apply 𝒟 i hq'.1 hqM, Submodule.coe_smul]
    have hx2 : (x : W M H) ∈ V 𝒟 i ⊓ ⨅ a : ↥(𝔸 M H S),
        Module.End.eigenspace (a : Module.End ℂ (W M H)) (χ a) := x.2
    rw [Submodule.mem_inf, Submodule.mem_iInf] at hx2
    simp only [φ, Submodule.coe_inclusion]
    have := hx2.2 ⟨CuspForm.heckeULinH 2 q, Algebra.subset_adjoin (Or.inr (Or.inl ⟨q, hq'.1, hqM, rfl⟩))⟩
    rw [Module.End.mem_eigenspace_iff] at this
    simp only [lam, dif_pos (And.intro hq'.1 hqM)]
    exact this
  calc Module.finrank ℂ ↥X = Module.finrank ℂ ↥(LinearMap.range φ) := (LinearMap.finrank_range_of_inj hφ).symm
    _ ≤ Module.finrank ℂ ↥Y := Submodule.finrank_mono hrange
    _ ≤ 1 := hle

end oneClass

theorem main (hSfin : S.Finite) :
    Nonempty (Module.Basis (Fin 1) ↥(𝔸 M H S) (W M H)) ∧
    ∀ χ : ↥(𝔸 M H S) →ₐ[ℂ] ℂ,
      Module.finrank ℂ ↥(⨅ a : ↥(𝔸 M H S), Module.End.eigenspace (a : Module.End ℂ (W M H)) (χ a)) = 1 := by
  classical
  obtain ⟨𝒟⟩ := nonempty_datum M H
  haveI := finiteDimensional 𝒟
  choose e he h1 h0 using exists_idempotents S 𝒟 hSfin
  exact Module.End.nonempty_basis_fin_one_and_finrank_iInf_eigenspace_eq_one_of_iSupIndep_of_cyclic
    (V 𝒟) (V_iSupIndep 𝒟) (V_iSup_eq_top 𝒟) (𝔸 M H S) (A_comm S 𝒟) (A_stab S 𝒟)
    (fun i => ⟨e i, he i⟩) h1 (fun i j hj => h0 i j hj) (fun i => 𝒟.G i (M / 𝒟.L i))
    (fun i => G_mem_V 𝒟 i dvd_rfl) (cyclic S 𝒟) (eigen_le_one S 𝒟)

end M8T

end

theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) (hSfin : S.Finite) :
    Nonempty (Module.Basis (Fin 1)
      ↥(Algebra.adjoin ℂ {T : Module.End ℂ (CuspForm (CohCarrier.GammaH M H) 2) |
          (∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ℓ ∉ S ∧ T = CuspForm.heckeTLinH 2 hℓ hℓM) ∨
          (∃ q : ℕ, q.Prime ∧ q ∣ M ∧ T = CuspForm.heckeULinH 2 q) ∨
          (∃ d : (ZMod M)ˣ, T = CuspForm.diamondLinH 2 d)})
      (CuspForm (CohCarrier.GammaH M H) 2)) ∧
    ∀ χ : ↥(Algebra.adjoin ℂ {T : Module.End ℂ (CuspForm (CohCarrier.GammaH M H) 2) |
          (∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ℓ ∉ S ∧ T = CuspForm.heckeTLinH 2 hℓ hℓM) ∨
          (∃ q : ℕ, q.Prime ∧ q ∣ M ∧ T = CuspForm.heckeULinH 2 q) ∨
          (∃ d : (ZMod M)ˣ, T = CuspForm.diamondLinH 2 d)}) →ₐ[ℂ] ℂ,
      Module.finrank ℂ ↥(⨅ a : ↥(Algebra.adjoin ℂ {T : Module.End ℂ (CuspForm (CohCarrier.GammaH M H) 2) |
          (∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ℓ ∉ S ∧ T = CuspForm.heckeTLinH 2 hℓ hℓM) ∨
          (∃ q : ℕ, q.Prime ∧ q ∣ M ∧ T = CuspForm.heckeULinH 2 q) ∨
          (∃ d : (ZMod M)ˣ, T = CuspForm.diamondLinH 2 d)}),
        Module.End.eigenspace (a : Module.End ℂ (CuspForm (CohCarrier.GammaH M H) 2)) (χ a)) = 1 :=
  M8T.main S hSfin

end S_CuspForm_nonempty_basis_fin_one_gammaH_and_finrank_eigenspace_eq_one
end P2MW
export P2MW.S_CuspForm_nonempty_basis_fin_one_gammaH_and_finrank_eigenspace_eq_one (solution)
