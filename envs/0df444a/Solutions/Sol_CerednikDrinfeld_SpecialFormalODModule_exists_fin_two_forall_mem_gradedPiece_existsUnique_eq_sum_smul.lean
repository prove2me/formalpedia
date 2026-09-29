-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.exists_fin_two_forall_mem_gradedPiece_existsUnique_eq_sum_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/726a3b25-699c-57fd-a373-304b64e962ac

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isCompl_lieZero_lieOne
import Theorems.Thm_MvFormalGroup_CartierModule_nonempty_basis_of_finrank_eq_pow
import Theorems.Thm_MvFormalGroup_CartierModule_map_injective_of_finite_quotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_forall_mem_gradedPiece_existsUnique_eq_sum_smul
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

universe u

namespace P2mKcGradedRank

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld CerednikDrinfeld.FormalODModule

variable {p : ℕ} [hp : Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectRing k p]
variable {j : Zp2 p →+* k} (Φ : SpecialFormalODModule p j)

local notation "𝕎" => WittVector p
local notation "M" => CartierModule p Φ.F

omit [CharP k p] [PerfectRing k p] in

theorem smul_mem_gradedPiece (n : ℕ) (w : 𝕎 k) (f : CartierModule p Φ.F)
    (hf : f ∈ Φ.toFormalODModule.gradedPiece j n) :
    w • f ∈ Φ.toFormalODModule.gradedPiece j n := by
  intro c
  have hfc := hf c
  rw [endAct_smul_witt, hfc, homothety_smul_witt]

def piece (n : ℕ) : Submodule (𝕎 k) (CartierModule p Φ.F) where
  carrier := Φ.toFormalODModule.gradedPiece j n
  add_mem' hf hg := (Φ.toFormalODModule.gradedPiece j n).add_mem hf hg
  zero_mem' := (Φ.toFormalODModule.gradedPiece j n).zero_mem
  smul_mem' w f hf := smul_mem_gradedPiece Φ n w f hf

omit [CharP k p] [PerfectRing k p] in
theorem mem_piece {n : ℕ} {f : CartierModule p Φ.F} :
    f ∈ piece Φ n ↔ f ∈ Φ.toFormalODModule.gradedPiece j n := Iff.rfl

omit [CharP k p] [PerfectRing k p] in
theorem piece_add_two (n : ℕ) : piece Φ (n + 2) = piece Φ n := by
  ext f
  rw [mem_piece, mem_piece, gradedPiece_add_two]

omit [CharP k p] [PerfectRing k p] in
theorem piece_eq_piece_mod_two (n : ℕ) : piece Φ n = piece Φ (n % 2) := by
  ext f
  rw [mem_piece, mem_piece]
  conv_lhs => rw [← Nat.mod_add_div n 2, gradedPiece_add_two_mul]

omit [PerfectRing k p] in

theorem grading :
    IsCompl (Φ.toFormalODModule.gradedPiece j 0) (Φ.toFormalODModule.gradedPiece j 1) ∧
    (∀ (n : ℕ) (g : CartierModule p Φ.F),
        verschiebung g ∈ Φ.toFormalODModule.gradedPiece j (n + 1) ↔
          g ∈ Φ.toFormalODModule.gradedPiece j n) ∧
    (∀ n, ∀ f ∈ Φ.toFormalODModule.gradedPiece j n,
        frobenius f ∈ Φ.toFormalODModule.gradedPiece j (n + 1)) := by
  obtain ⟨h1, h2, h3, -⟩ :=
    isCompl_gradedPiece_zero_one_of_isCompl_lieZero_lieOne p j Φ.toFormalODModule Φ.isSpecial.1
  exact ⟨h1, h2, h3⟩

omit [PerfectRing k p] in

theorem isCompl_piece : IsCompl (piece Φ 0) (piece Φ 1) := by
  have h := (grading Φ).1
  refine isCompl_iff.mpr ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro f hf0 hf1
    exact AddSubgroup.disjoint_def.mp h.disjoint hf0 hf1
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro f
    have hsup : f ∈ Φ.toFormalODModule.gradedPiece j 0 ⊔ Φ.toFormalODModule.gradedPiece j 1 := by
      rw [codisjoint_iff.mp h.codisjoint]; trivial
    obtain ⟨y, hy, z, hz, hyz⟩ := AddSubgroup.mem_sup.mp hsup
    exact Submodule.mem_sup.mpr ⟨y, hy, z, hz, hyz⟩

omit [CharP k p] [PerfectRing k p] in

theorem finrank_kerAlgebra :
    Module.finrank k (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range (Φ.F.nthSeries p))) = p ^ 4 := by
  have h := Φ.hasHeight.2.2 k (RingHom.id k)
  have hmap : (Φ.act (p : Zp2 p)).map (RingHom.id k) = Φ.F.nthSeries p := by
    funext i
    show MvPowerSeries.map (RingHom.id k) (Φ.act (p : Zp2 p) i) = Φ.F.nthSeries p i
    rw [MvPowerSeries.map_id, ← Φ.act_natCast]
    rfl
  rw [hmap] at h
  exact h

theorem nonempty_basis_four : Nonempty (Module.Basis (Fin 4) (𝕎 k) (CartierModule p Φ.F)) :=
  nonempty_basis_of_finrank_eq_pow p Φ.F 4 (finrank_kerAlgebra Φ)

omit [CharP k p] [PerfectRing k p] in
theorem finite_kerAlgebra :
    Module.Finite k (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range (Φ.F.nthSeries p))) :=
  Module.finite_of_finrank_pos (by rw [finrank_kerAlgebra Φ]; exact pow_pos hp.out.pos 4)

omit [CharP k p] [PerfectRing k p] in

theorem smul_p_injective :
    Function.Injective (fun f : CartierModule p Φ.F => (p : 𝕎 k) • f) := by
  have hinj : Function.Injective (map (p := p) ((p : ℕ) : MvFormalGroup.End Φ.F)) := by
    refine map_injective_of_finite_quotient p Φ.F Φ.F _ ?_
    rw [MvFormalGroup.End.toPowerSeries_natCast]
    exact finite_kerAlgebra Φ
  intro f g hfg
  apply hinj
  have hdict : ∀ x : CartierModule p Φ.F,
      (p : 𝕎 k) • x = map ((p : ℕ) : MvFormalGroup.End Φ.F) x := fun x => by
    rw [natCast_smul_eq_nsmul', ← endAct_natCast]
    rfl
  have h' : (p : 𝕎 k) • f = (p : 𝕎 k) • g := hfg
  rwa [hdict, hdict] at h'

section Pieces

variable (a b : ℕ) (hab : IsCompl (piece Φ a) (piece Φ b))
include hab

theorem free_and_finite_of_isCompl :
    Module.Free (𝕎 k) (piece Φ a) ∧ Module.Finite (𝕎 k) (piece Φ a) := by
  obtain ⟨B⟩ := nonempty_basis_four Φ
  haveI : Module.Free (𝕎 k) (CartierModule p Φ.F) := Module.Free.of_basis B
  haveI : Module.Finite (𝕎 k) (CartierModule p Φ.F) := Module.Finite.of_basis B
  let e := Submodule.prodEquivOfIsCompl _ _ hab
  let s : CartierModule p Φ.F →ₗ[𝕎 k] piece Φ a := (LinearMap.fst _ _ _).comp e.symm.toLinearMap
  have hs : s ∘ₗ (piece Φ a).subtype = LinearMap.id := by
    ext x
    simp [s, e]
  have hsurj : Function.Surjective s := fun x => ⟨(piece Φ a).subtype x, by
    have := LinearMap.congr_fun hs x; simpa using this⟩
  haveI hfin : Module.Finite (𝕎 k) (piece Φ a) := Module.Finite.of_surjective s hsurj
  haveI : Module.Projective (𝕎 k) (piece Φ a) := Module.Projective.of_split _ _ hs
  exact ⟨Module.free_of_flat_of_isLocalRing, hfin⟩

end Pieces

theorem free_piece_zero : Module.Free (𝕎 k) (piece Φ 0) :=
  (free_and_finite_of_isCompl Φ 0 1 (isCompl_piece Φ)).1
theorem finite_piece_zero : Module.Finite (𝕎 k) (piece Φ 0) :=
  (free_and_finite_of_isCompl Φ 0 1 (isCompl_piece Φ)).2
theorem free_piece_one : Module.Free (𝕎 k) (piece Φ 1) :=
  (free_and_finite_of_isCompl Φ 1 0 (isCompl_piece Φ).symm).1
theorem finite_piece_one : Module.Finite (𝕎 k) (piece Φ 1) :=
  (free_and_finite_of_isCompl Φ 1 0 (isCompl_piece Φ).symm).2

theorem finrank_add :
    Module.finrank (𝕎 k) (piece Φ 0) + Module.finrank (𝕎 k) (piece Φ 1) = 4 := by
  obtain ⟨B⟩ := nonempty_basis_four Φ
  haveI := free_piece_zero Φ
  haveI := free_piece_one Φ
  haveI := finite_piece_zero Φ
  haveI := finite_piece_one Φ
  rw [← Module.finrank_prod, LinearEquiv.finrank_eq (Submodule.prodEquivOfIsCompl _ _ (isCompl_piece Φ)),
    Module.finrank_eq_card_basis B, Fintype.card_fin]

def vPiece : Submodule (𝕎 k) (CartierModule p Φ.F) where
  carrier := {g | ∃ f ∈ piece Φ 0, verschiebung f = g}
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨f', hf', rfl⟩
    exact ⟨f + f', (piece Φ 0).add_mem hf hf', map_add _ _ _⟩
  zero_mem' := ⟨0, (piece Φ 0).zero_mem, map_zero _⟩
  smul_mem' := by
    rintro w _ ⟨f, hf, rfl⟩
    exact ⟨WittVector.frobenius w • f, (piece Φ 0).smul_mem _ hf, (smul_verschiebung w f).symm⟩

omit [PerfectRing k p] in
theorem vPiece_le : vPiece Φ ≤ piece Φ 1 := by
  rintro _ ⟨f, hf, rfl⟩
  exact ((grading Φ).2.1 0 f).mpr hf

omit [PerfectRing k p] in

theorem smul_p_mem_vPiece {g : CartierModule p Φ.F} (hg : g ∈ piece Φ 1) :
    (p : 𝕎 k) • g ∈ vPiece Φ := by
  refine ⟨frobenius g, ?_, verschiebung_frobenius_eq_smul g⟩
  have h2 : frobenius g ∈ Φ.toFormalODModule.gradedPiece j (1 + 1) := (grading Φ).2.2 1 g hg
  rw [mem_piece, ← gradedPiece_add_two]
  exact h2

theorem finrank_vPiece :
    Module.finrank (𝕎 k) (vPiece Φ) = Module.finrank (𝕎 k) (piece Φ 0) ∧
      Module.Finite (𝕎 k) (vPiece Φ) := by
  haveI := free_piece_zero Φ
  haveI := finite_piece_zero Φ

  let ι := Module.Free.ChooseBasisIndex (𝕎 k) (piece Φ 0)
  let B : Module.Basis ι (𝕎 k) (piece Φ 0) := Module.Free.chooseBasis _ _
  haveI : Fintype ι := inferInstance

  let e : ι → vPiece Φ := fun i => ⟨verschiebung (B i : CartierModule p Φ.F), B i, (B i).2, rfl⟩
  have he : ∀ i, ((e i : vPiece Φ) : CartierModule p Φ.F) = verschiebung (B i : CartierModule p Φ.F) :=
    fun i => rfl

  have hV : ∀ a : ι → 𝕎 k, ((∑ i, a i • e i : vPiece Φ) : CartierModule p Φ.F) =
      verschiebung ((∑ i, WittVector.frobenius (a i) • B i : piece Φ 0) : CartierModule p Φ.F) := by
    intro a
    rw [Submodule.coe_sum, Submodule.coe_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, Submodule.coe_smul, he, smul_verschiebung]
  have hli : LinearIndependent (𝕎 k) e := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    have h0 : verschiebung ((∑ i, WittVector.frobenius (a i) • B i : piece Φ 0) :
        CartierModule p Φ.F) = 0 := by
      rw [← hV, ha]; rfl
    have h1 : ((∑ i, WittVector.frobenius (a i) • B i : piece Φ 0) : CartierModule p Φ.F) = 0 :=
      verschiebung_injective (h0.trans (map_zero _).symm)
    have h2 : (∑ i, WittVector.frobenius (a i) • B i : piece Φ 0) = 0 := Subtype.ext h1
    have h3 := Fintype.linearIndependent_iff.mp B.linearIndependent _ h2 i
    exact (WittVector.frobenius_bijective p k).1 (h3.trans (map_zero _).symm)
  have hsp : ⊤ ≤ Submodule.span (𝕎 k) (Set.range e) := by
    rintro ⟨g, f, hf, rfl⟩ -

    have hf' : (⟨f, hf⟩ : piece Φ 0) = ∑ i, B.repr ⟨f, hf⟩ i • B i := (B.sum_repr _).symm
    let a : ι → 𝕎 k := fun i => (WittVector.frobeniusEquiv p k).symm (B.repr ⟨f, hf⟩ i)
    have ha : ∀ i, WittVector.frobenius (a i) = B.repr ⟨f, hf⟩ i := fun i => by
      show (WittVector.frobeniusEquiv p k) ((WittVector.frobeniusEquiv p k).symm _) = _
      exact (WittVector.frobeniusEquiv p k).apply_symm_apply _
    have hsum : (⟨verschiebung f, f, hf, rfl⟩ : vPiece Φ) = ∑ i, a i • e i := by
      apply Subtype.ext
      rw [hV]
      show verschiebung f = _
      congr 1
      have := congrArg (fun x : piece Φ 0 => (x : CartierModule p Φ.F)) hf'
      simp only at this
      rw [this]
      simp_rw [ha]
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let B' : Module.Basis ι (𝕎 k) (vPiece Φ) := Module.Basis.mk hli hsp
  exact ⟨by rw [Module.finrank_eq_card_basis B', Module.finrank_eq_card_basis B],
    Module.Finite.of_basis B'⟩

theorem finrank_piece_zero_eq_one :
    Module.finrank (𝕎 k) (piece Φ 0) = Module.finrank (𝕎 k) (piece Φ 1) := by
  haveI := finite_piece_one Φ
  obtain ⟨hV, hVfin⟩ := finrank_vPiece Φ
  haveI := hVfin
  apply le_antisymm
  · rw [← hV]
    exact Submodule.finrank_mono (vPiece_le Φ)
  ·
    let ψ : piece Φ 1 →ₗ[𝕎 k] vPiece Φ :=
      { toFun := fun g => ⟨(p : 𝕎 k) • (g : CartierModule p Φ.F), smul_p_mem_vPiece Φ g.2⟩
        map_add' := fun g g' => Subtype.ext (smul_add _ _ _)
        map_smul' := fun w g => Subtype.ext (smul_comm _ _ _) }
    have hψ : Function.Injective ψ := fun g g' h =>
      Subtype.ext (smul_p_injective Φ (congrArg (fun x : vPiece Φ => (x : CartierModule p Φ.F)) h))
    calc Module.finrank (𝕎 k) (piece Φ 1)
        = Module.finrank (𝕎 k) (LinearMap.range ψ) := (LinearMap.finrank_range_of_inj hψ).symm
      _ ≤ Module.finrank (𝕎 k) (vPiece Φ) := Submodule.finrank_le _
      _ = Module.finrank (𝕎 k) (piece Φ 0) := hV

theorem finrank_piece_eq_two (n : ℕ) : Module.finrank (𝕎 k) (piece Φ n) = 2 := by
  have h0 : Module.finrank (𝕎 k) (piece Φ 0) = 2 := by
    have := finrank_add Φ; rw [← finrank_piece_zero_eq_one Φ] at this; omega
  rw [piece_eq_piece_mod_two]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [h]; exact h0
  · rw [h, ← finrank_piece_zero_eq_one Φ]; exact h0

theorem free_piece (n : ℕ) : Module.Free (𝕎 k) (piece Φ n) ∧ Module.Finite (𝕎 k) (piece Φ n) := by
  rw [piece_eq_piece_mod_two]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [h]; exact ⟨free_piece_zero Φ, finite_piece_zero Φ⟩
  · rw [h]; exact ⟨free_piece_one Φ, finite_piece_one Φ⟩

noncomputable def basisTwo (n : ℕ) : Module.Basis (Fin 2) (𝕎 k) (piece Φ n) :=
  haveI := (free_piece Φ n).1
  haveI := (free_piece Φ n).2
  Module.finBasisOfFinrankEq _ _ (finrank_piece_eq_two Φ n)

end P2mKcGradedRank

open P2mKcGradedRank MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld in
theorem solution
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectRing k p]
    (j : CerednikDrinfeld.Zp2 p →+* k) (Φ : CerednikDrinfeld.SpecialFormalODModule p j) (n : ℕ) :
    (∀ (w : WittVector p k) (f : MvFormalGroup.CartierModule p Φ.F),
        f ∈ Φ.gradedPiece j n → w • f ∈ Φ.gradedPiece j n) ∧
    ∃ e : Fin 2 → MvFormalGroup.CartierModule p Φ.F,
      (∀ r, e r ∈ Φ.gradedPiece j n) ∧
      ∀ f ∈ Φ.gradedPiece j n, ∃! w : Fin 2 → WittVector p k, f = ∑ r, w r • e r := by
  refine ⟨fun w f hf => smul_mem_gradedPiece Φ n w f hf, ?_⟩
  let B := basisTwo Φ n
  refine ⟨fun r => (B r : MvFormalGroup.CartierModule p Φ.F), fun r => (B r).2, fun f hf => ?_⟩
  have hcoe : ∀ w : Fin 2 → WittVector p k,
      ((B.equivFun.symm w : piece Φ n) : MvFormalGroup.CartierModule p Φ.F) =
        ∑ r, w r • (B r : MvFormalGroup.CartierModule p Φ.F) := fun w => by
    rw [Module.Basis.equivFun_symm_apply, Submodule.coe_sum]
    simp only [Submodule.coe_smul]
  refine ⟨B.equivFun ⟨f, hf⟩, ?_, fun w hw => ?_⟩
  · show f = ∑ r, B.equivFun ⟨f, hf⟩ r • (B r : MvFormalGroup.CartierModule p Φ.F)
    have := hcoe (B.equivFun ⟨f, hf⟩)
    rw [LinearEquiv.symm_apply_apply] at this
    exact (this : f = _)
  · have h1 : (⟨f, hf⟩ : piece Φ n) = B.equivFun.symm w := Subtype.ext (by rw [hcoe]; exact hw)
    rw [h1, LinearEquiv.apply_symm_apply]

end S_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_forall_mem_gradedPiece_existsUnique_eq_sum_smul
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_forall_mem_gradedPiece_existsUnique_eq_sum_smul (solution)
