-- Prove2me | solution 1 for CerednikDrinfeld.GradedCartierModuleData.exists_dominating_of_apply_basis_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/21fc9ceb-b08f-5f5e-a7a0-8962f72fed16

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_isHomogeneousVBasis_map_of_baseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_dominating_of_apply_basis_eq

set_option autoImplicit false

noncomputable section

namespace P2mAbsDom

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData

theorem witt_map_frobenius {p : ℕ} [Fact p.Prime] {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (w : WittVector p R) :
    WittVector.map f (WittVector.frobenius w) = WittVector.frobenius (WittVector.map f w) :=
  WittVector.IsPoly.map (WittVector.frobenius_isPoly p) f w

theorem witt_map_map {p : ℕ} [Fact p.Prime] {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (w : WittVector p R) :
    WittVector.map g (WittVector.map f w) = WittVector.map (g.comp f) w := by
  ext n; simp [WittVector.map_coeff]

theorem semiconj_iterate {α β : Type} (f : α → β) (ga : α → α) (gb : β → β)
    (h : ∀ x, f (ga x) = gb (f x)) (n : ℕ) (x : α) : f (ga^[n] x) = gb^[n] (f x) :=
  Function.Semiconj.iterate_right (f := f) (ga := ga) (gb := gb) h n x

structure Glue (p : ℕ) [Fact p.Prime] (B S₁ S₂ : Type) [CommRing B] [CommRing S₁] [CommRing S₂]
    (j : Zp2 p →+* B) (j₁ : Zp2 p →+* S₁) (j₂ : Zp2 p →+* S₂) : Type 1 where
  q₁ : S₁ →+* B
  q₂ : S₂ →+* B
  hq₁ : q₁.comp j₁ = j
  hq₂ : q₂.comp j₂ = j
  D : GradedCartierModuleData p B j
  D₁ : GradedCartierModuleData p S₁ j₁
  D₂ : GradedCartierModuleData p S₂ j₂
  f₁ : D₁.M →+ D.M
  f₂ : D₂.M →+ D.M
  hf₁ : IsBaseChangeAlong' q₁ D₁ D f₁
  hf₂ : IsBaseChangeAlong' q₂ D₂ D f₂

namespace Glue

variable {p : ℕ} [Fact p.Prime] {B S₁ S₂ : Type} [CommRing B] [CommRing S₁] [CommRing S₂]
    {j : Zp2 p →+* B} {j₁ : Zp2 p →+* S₁} {j₂ : Zp2 p →+* S₂}
    (G : Glue p B S₁ S₂ j j₁ j₂)

def S3 : Subring (S₁ × S₂) :=
  RingHom.eqLocus (G.q₁.comp (RingHom.fst S₁ S₂)) (G.q₂.comp (RingHom.snd S₁ S₂))

theorem mem_S3 {x : S₁ × S₂} : x ∈ G.S3 ↔ G.q₁ x.1 = G.q₂ x.2 := Iff.rfl

def r₁ : (G.S3 : Type) →+* S₁ := (RingHom.fst S₁ S₂).comp G.S3.subtype
def r₂ : (G.S3 : Type) →+* S₂ := (RingHom.snd S₁ S₂).comp G.S3.subtype

@[scoped simp] theorem r₁_apply (s : G.S3) : G.r₁ s = s.1.1 := rfl
@[scoped simp] theorem r₂_apply (s : G.S3) : G.r₂ s = s.1.2 := rfl

def j₃ : Zp2 p →+* (G.S3 : Type) :=
  (j₁.prod j₂).codRestrict G.S3 (fun z => by
    show G.q₁ (j₁ z) = G.q₂ (j₂ z)
    rw [← RingHom.comp_apply, G.hq₁, ← RingHom.comp_apply, G.hq₂])

theorem r₁_comp_j₃ : G.r₁.comp G.j₃ = j₁ := RingHom.ext fun _ => rfl
theorem r₂_comp_j₃ : G.r₂.comp G.j₃ = j₂ := RingHom.ext fun _ => rfl
theorem q_comp_r : G.q₁.comp G.r₁ = G.q₂.comp G.r₂ := RingHom.ext fun s => s.2

theorem torsionFree (hS₁ : ∀ s : S₁, (p : S₁) * s = 0 → s = 0)
    (hS₂ : ∀ s : S₂, (p : S₂) * s = 0 → s = 0) :
    ∀ s : G.S3, (p : G.S3) * s = 0 → s = 0 := by
  intro s hs
  have h := congrArg Subtype.val hs
  simp only [Subring.coe_mul, Subring.coe_natCast, Subring.coe_zero, Prod.ext_iff, Prod.fst_mul,
    Prod.snd_mul, Prod.fst_natCast, Prod.snd_natCast, Prod.fst_zero, Prod.snd_zero] at h
  exact Subtype.ext (Prod.ext (hS₁ _ h.1) (hS₂ _ h.2))

def M3 : AddSubgroup (G.D₁.M × G.D₂.M) where
  carrier := {x | G.f₁ x.1 = G.f₂ x.2}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, map_add] at ha hb ⊢
    rw [ha, hb]
  zero_mem' := by simp
  neg_mem' {a} ha := by
    simp only [Set.mem_setOf_eq, Prod.fst_neg, Prod.snd_neg, map_neg] at ha ⊢
    rw [ha]

theorem mem_M3 {x : G.D₁.M × G.D₂.M} : x ∈ G.M3 ↔ G.f₁ x.1 = G.f₂ x.2 := Iff.rfl

def π₁ : (G.M3 : Type) →+ G.D₁.M := (AddMonoidHom.fst _ _).comp G.M3.subtype
def π₂ : (G.M3 : Type) →+ G.D₂.M := (AddMonoidHom.snd _ _).comp G.M3.subtype

@[scoped simp] theorem π₁_apply (x : G.M3) : G.π₁ x = x.1.1 := rfl
@[scoped simp] theorem π₂_apply (x : G.M3) : G.π₂ x = x.1.2 := rfl

theorem ext3 {x y : G.M3} (h₁ : x.1.1 = y.1.1) (h₂ : x.1.2 = y.1.2) : x = y :=
  Subtype.ext (Prod.ext h₁ h₂)

theorem rel (x : G.M3) : G.f₁ x.1.1 = G.f₂ x.1.2 := x.2

theorem f₁_smul (w : WittVector p S₁) (x : G.D₁.M) :
    G.f₁ (w • x) = WittVector.map G.q₁ w • G.f₁ x := G.hf₁.1 w x
theorem f₂_smul (w : WittVector p S₂) (x : G.D₂.M) :
    G.f₂ (w • x) = WittVector.map G.q₂ w • G.f₂ x := G.hf₂.1 w x
theorem f₁_F (x : G.D₁.M) : G.f₁ (G.D₁.frobenius x) = G.D.frobenius (G.f₁ x) := G.hf₁.2.1 x
theorem f₂_F (x : G.D₂.M) : G.f₂ (G.D₂.frobenius x) = G.D.frobenius (G.f₂ x) := G.hf₂.2.1 x
theorem f₁_V (x : G.D₁.M) : G.f₁ (G.D₁.verschiebung x) = G.D.verschiebung (G.f₁ x) :=
  G.hf₁.2.2.1 x
theorem f₂_V (x : G.D₂.M) : G.f₂ (G.D₂.verschiebung x) = G.D.verschiebung (G.f₂ x) :=
  G.hf₂.2.2.1 x
theorem f₁_Pi (x : G.D₁.M) : G.f₁ (G.D₁.varpi x) = G.D.varpi (G.f₁ x) := G.hf₁.2.2.2.1 x
theorem f₂_Pi (x : G.D₂.M) : G.f₂ (G.D₂.varpi x) = G.D.varpi (G.f₂ x) := G.hf₂.2.2.2.1 x
theorem f₁_piece (i : Fin 2) (x : G.D₁.M) (hx : x ∈ G.D₁.piece i) : G.f₁ x ∈ G.D.piece i :=
  G.hf₁.2.2.2.2.1 i x hx
theorem f₂_piece (i : Fin 2) (x : G.D₂.M) (hx : x ∈ G.D₂.piece i) : G.f₂ x ∈ G.D.piece i :=
  G.hf₂.2.2.2.2.1 i x hx

theorem map_q_r (w : WittVector p G.S3) :
    WittVector.map G.q₁ (WittVector.map G.r₁ w) = WittVector.map G.q₂ (WittVector.map G.r₂ w) := by
  rw [witt_map_map, witt_map_map, G.q_comp_r]

scoped instance instSMul : SMul (WittVector p G.S3) G.M3 where
  smul w x := ⟨(WittVector.map G.r₁ w • x.1.1, WittVector.map G.r₂ w • x.1.2), by
    show G.f₁ _ = G.f₂ _
    rw [G.f₁_smul, G.f₂_smul, G.map_q_r, G.rel x]⟩

@[scoped simp] theorem smul_fst (w : WittVector p G.S3) (x : G.M3) :
    (w • x).1.1 = WittVector.map G.r₁ w • x.1.1 := rfl
@[scoped simp] theorem smul_snd (w : WittVector p G.S3) (x : G.M3) :
    (w • x).1.2 = WittVector.map G.r₂ w • x.1.2 := rfl

theorem coe_add3 (x y : G.M3) : (x + y).1 = x.1 + y.1 := rfl

theorem m_smul_add (r : WittVector p G.S3) (x y : G.M3) : r • (x + y) = r • x + r • y :=
  G.ext3 (by simp only [smul_fst, coe_add3, Prod.fst_add, smul_add])
    (by simp only [smul_snd, coe_add3, Prod.snd_add, smul_add])

theorem m_add_smul (r s : WittVector p G.S3) (x : G.M3) : (r + s) • x = r • x + s • x :=
  G.ext3 (by simp only [smul_fst, coe_add3, Prod.fst_add, map_add, add_smul])
    (by simp only [smul_snd, coe_add3, Prod.snd_add, map_add, add_smul])

theorem m_mul_smul (r s : WittVector p G.S3) (x : G.M3) : (r * s) • x = r • s • x :=
  G.ext3 (by simp only [smul_fst, map_mul, mul_smul])
    (by simp only [smul_snd, map_mul, mul_smul])

theorem m_one_smul (x : G.M3) : (1 : WittVector p G.S3) • x = x :=
  G.ext3 (by simp only [smul_fst, map_one, one_smul])
    (by simp only [smul_snd, map_one, one_smul])

scoped instance instModule : Module (WittVector p G.S3) G.M3 :=
  Module.ofMinimalAxioms G.m_smul_add G.m_add_smul G.m_mul_smul G.m_one_smul

def F3 : (G.M3 : Type) →+ G.M3 where
  toFun x := ⟨(G.D₁.frobenius x.1.1, G.D₂.frobenius x.1.2), by
    show G.f₁ _ = G.f₂ _; rw [G.f₁_F, G.f₂_F, G.rel x]⟩
  map_zero' := by apply G.ext3 <;> simp
  map_add' x y := by apply G.ext3 <;> simp

def V3 : (G.M3 : Type) →+ G.M3 where
  toFun x := ⟨(G.D₁.verschiebung x.1.1, G.D₂.verschiebung x.1.2), by
    show G.f₁ _ = G.f₂ _; rw [G.f₁_V, G.f₂_V, G.rel x]⟩
  map_zero' := by apply G.ext3 <;> simp
  map_add' x y := by apply G.ext3 <;> simp

def Pi3 : (G.M3 : Type) →ₗ[WittVector p G.S3] G.M3 where
  toFun x := ⟨(G.D₁.varpi x.1.1, G.D₂.varpi x.1.2), by
    show G.f₁ _ = G.f₂ _; rw [G.f₁_Pi, G.f₂_Pi, G.rel x]⟩
  map_add' x y := by apply G.ext3 <;> simp
  map_smul' w x := by apply G.ext3 <;> simp

@[scoped simp] theorem F3_fst (x : G.M3) : (G.F3 x).1.1 = G.D₁.frobenius x.1.1 := rfl
@[scoped simp] theorem F3_snd (x : G.M3) : (G.F3 x).1.2 = G.D₂.frobenius x.1.2 := rfl
@[scoped simp] theorem V3_fst (x : G.M3) : (G.V3 x).1.1 = G.D₁.verschiebung x.1.1 := rfl
@[scoped simp] theorem V3_snd (x : G.M3) : (G.V3 x).1.2 = G.D₂.verschiebung x.1.2 := rfl
@[scoped simp] theorem Pi3_fst (x : G.M3) : (G.Pi3 x).1.1 = G.D₁.varpi x.1.1 := rfl
@[scoped simp] theorem Pi3_snd (x : G.M3) : (G.Pi3 x).1.2 = G.D₂.varpi x.1.2 := rfl

def piece3 (i : Fin 2) : Submodule (WittVector p G.S3) G.M3 where
  carrier := {x | x.1.1 ∈ G.D₁.piece i ∧ x.1.2 ∈ G.D₂.piece i}
  add_mem' {a b} ha hb := by
    refine ⟨?_, ?_⟩
    · have := add_mem ha.1 hb.1; simpa using this
    · have := add_mem ha.2 hb.2; simpa using this
  zero_mem' := by refine ⟨?_, ?_⟩ <;> simp
  smul_mem' w x hx := ⟨by simpa using Submodule.smul_mem _ _ hx.1,
    by simpa using Submodule.smul_mem _ _ hx.2⟩

theorem mem_piece3 {i : Fin 2} {x : G.M3} :
    x ∈ G.piece3 i ↔ x.1.1 ∈ G.D₁.piece i ∧ x.1.2 ∈ G.D₂.piece i := Iff.rfl

theorem ax_frobenius_smul (w : WittVector p G.S3) (x : G.M3) :
    G.F3 (w • x) = WittVector.frobenius w • G.F3 x := by
  apply G.ext3
  · simp [G.D₁.frobenius_smul, witt_map_frobenius]
  · simp [G.D₂.frobenius_smul, witt_map_frobenius]

theorem ax_smul_verschiebung (w : WittVector p G.S3) (x : G.M3) :
    w • G.V3 x = G.V3 (WittVector.frobenius w • x) := by
  apply G.ext3
  · simp [G.D₁.smul_verschiebung, witt_map_frobenius]
  · simp [G.D₂.smul_verschiebung, witt_map_frobenius]

theorem ax_verschiebung_smul_frobenius (w : WittVector p G.S3) (x : G.M3) :
    G.V3 (w • G.F3 x) = WittVector.verschiebung w • x := by
  apply G.ext3
  · simp [G.D₁.verschiebung_smul_frobenius]
  · simp [G.D₂.verschiebung_smul_frobenius]

theorem nsmul_fst (n : ℕ) (x : G.M3) : (n • x).1.1 = n • x.1.1 := by simp
theorem nsmul_snd (n : ℕ) (x : G.M3) : (n • x).1.2 = n • x.1.2 := by simp

theorem ax_frobenius_verschiebung (x : G.M3) : G.F3 (G.V3 x) = (p : ℕ) • x := by
  apply G.ext3
  · rw [G.nsmul_fst]; simp [G.D₁.frobenius_verschiebung]
  · rw [G.nsmul_snd]; simp [G.D₂.frobenius_verschiebung]

theorem ax_varpi_verschiebung (x : G.M3) : G.Pi3 (G.V3 x) = G.V3 (G.Pi3 x) := by
  apply G.ext3
  · simp [G.D₁.varpi_verschiebung]
  · simp [G.D₂.varpi_verschiebung]

theorem ax_varpi_frobenius (x : G.M3) : G.Pi3 (G.F3 x) = G.F3 (G.Pi3 x) := by
  apply G.ext3
  · simp [G.D₁.varpi_frobenius]
  · simp [G.D₂.varpi_frobenius]

theorem ax_varpi_varpi (x : G.M3) : G.Pi3 (G.Pi3 x) = (p : ℕ) • x := by
  apply G.ext3
  · rw [G.nsmul_fst]; simp [G.D₁.varpi_varpi]
  · rw [G.nsmul_snd]; simp [G.D₂.varpi_varpi]

theorem piece_unique {R : Type} [CommRing R] {jR : Zp2 p →+* R} (E : GradedCartierModuleData p R jR)
    {a₀ a₁ b₀ b₁ : E.M} (ha₀ : a₀ ∈ E.piece 0) (ha₁ : a₁ ∈ E.piece 1)
    (hb₀ : b₀ ∈ E.piece 0) (hb₁ : b₁ ∈ E.piece 1) (h : a₀ + a₁ = b₀ + b₁) :
    a₀ = b₀ ∧ a₁ = b₁ := by
  have hdis := Submodule.disjoint_def.1 E.isCompl_piece.disjoint
  have e : a₀ - b₀ = b₁ - a₁ := by rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
  have h0 : a₀ - b₀ ∈ E.piece 0 := sub_mem ha₀ hb₀
  have h1 : a₀ - b₀ ∈ E.piece 1 := by rw [e]; exact sub_mem hb₁ ha₁
  have hz : a₀ - b₀ = 0 := hdis _ h0 h1
  have ha : a₀ = b₀ := sub_eq_zero.1 hz
  refine ⟨ha, ?_⟩
  rw [ha] at h
  exact add_left_cancel h

theorem ax_isCompl_piece : IsCompl (G.piece3 0) (G.piece3 1) := by
  rw [isCompl_iff]
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hx0 hx1
    have d₁ := Submodule.disjoint_def.1 G.D₁.isCompl_piece.disjoint
    have d₂ := Submodule.disjoint_def.1 G.D₂.isCompl_piece.disjoint
    apply G.ext3
    · simpa using d₁ _ hx0.1 hx1.1
    · simpa using d₂ _ hx0.2 hx1.2
  · rw [Submodule.codisjoint_iff_exists_add_eq]
    intro z
    obtain ⟨a₀, a₁, ha₀, ha₁, ha⟩ :=
      (Submodule.codisjoint_iff_exists_add_eq.1 G.D₁.isCompl_piece.codisjoint) z.1.1
    obtain ⟨b₀, b₁, hb₀, hb₁, hb⟩ :=
      (Submodule.codisjoint_iff_exists_add_eq.1 G.D₂.isCompl_piece.codisjoint) z.1.2
    have key : G.f₁ a₀ + G.f₁ a₁ = G.f₂ b₀ + G.f₂ b₁ := by
      rw [← map_add, ← map_add, ha, hb]; exact G.rel z
    have hu := piece_unique G.D (G.f₁_piece 0 _ ha₀) (G.f₁_piece 1 _ ha₁) (G.f₂_piece 0 _ hb₀)
      (G.f₂_piece 1 _ hb₁) key
    refine ⟨⟨(a₀, b₀), hu.1⟩, ⟨(a₁, b₁), hu.2⟩, ⟨ha₀, hb₀⟩, ⟨ha₁, hb₁⟩, ?_⟩
    apply G.ext3
    · simpa using ha
    · simpa using hb

theorem ax_verschiebung_mem (i : Fin 2) (x : G.M3) (hx : x ∈ G.piece3 i) :
    G.V3 x ∈ G.piece3 (i + 1) :=
  ⟨G.D₁.verschiebung_mem i _ hx.1, G.D₂.verschiebung_mem i _ hx.2⟩

theorem ax_frobenius_mem (i : Fin 2) (x : G.M3) (hx : x ∈ G.piece3 i) :
    G.F3 x ∈ G.piece3 (i + 1) :=
  ⟨G.D₁.frobenius_mem i _ hx.1, G.D₂.frobenius_mem i _ hx.2⟩

theorem ax_varpi_mem (i : Fin 2) (x : G.M3) (hx : x ∈ G.piece3 i) :
    G.Pi3 x ∈ G.piece3 (i + 1) :=
  ⟨G.D₁.varpi_mem i _ hx.1, G.D₂.varpi_mem i _ hx.2⟩

@[reducible] def D3 : GradedCartierModuleData p G.S3 G.j₃ where
  M := G.M3
  frobenius := G.F3
  verschiebung := G.V3
  varpi := G.Pi3
  piece := G.piece3
  frobenius_smul := G.ax_frobenius_smul
  smul_verschiebung := G.ax_smul_verschiebung
  verschiebung_smul_frobenius := G.ax_verschiebung_smul_frobenius
  frobenius_verschiebung := G.ax_frobenius_verschiebung
  varpi_verschiebung := G.ax_varpi_verschiebung
  varpi_frobenius := G.ax_varpi_frobenius
  varpi_varpi := G.ax_varpi_varpi
  isCompl_piece := G.ax_isCompl_piece
  verschiebung_mem := G.ax_verschiebung_mem
  frobenius_mem := G.ax_frobenius_mem
  varpi_mem := G.ax_varpi_mem

theorem D3_M : G.D3.M = G.M3 := rfl
theorem D3_V : G.D3.verschiebung = G.V3 := rfl
theorem D3_F : G.D3.frobenius = G.F3 := rfl
theorem D3_Pi : G.D3.varpi = G.Pi3 := rfl
theorem D3_piece : G.D3.piece = G.piece3 := rfl

theorem π₁_iterV (n : ℕ) (x : G.M3) :
    (G.V3^[n] x).1.1 = G.D₁.verschiebung^[n] x.1.1 :=
  semiconj_iterate (fun z : G.M3 => z.1.1) G.V3 G.D₁.verschiebung (fun _ => rfl) n x
theorem π₂_iterV (n : ℕ) (x : G.M3) :
    (G.V3^[n] x).1.2 = G.D₂.verschiebung^[n] x.1.2 :=
  semiconj_iterate (fun z : G.M3 => z.1.2) G.V3 G.D₂.verschiebung (fun _ => rfl) n x
theorem f₁_iterV (n : ℕ) (x : G.D₁.M) :
    G.f₁ (G.D₁.verschiebung^[n] x) = G.D.verschiebung^[n] (G.f₁ x) :=
  semiconj_iterate G.f₁ G.D₁.verschiebung G.D.verschiebung G.f₁_V n x
theorem f₂_iterV (n : ℕ) (x : G.D₂.M) :
    G.f₂ (G.D₂.verschiebung^[n] x) = G.D.verschiebung^[n] (G.f₂ x) :=
  semiconj_iterate G.f₂ G.D₂.verschiebung G.D.verschiebung G.f₂_V n x

section basis

variable (γ₁ : Fin 2 → G.D₁.M) (γ₂ : Fin 2 → G.D₂.M)

def γ₃ (hγ : ∀ i : Fin 2, G.f₁ (γ₁ i) = G.f₂ (γ₂ i)) : Fin 2 → G.M3 := fun i => ⟨(γ₁ i, γ₂ i), hγ i⟩

@[scoped simp] theorem γ₃_fst (hγ : ∀ i : Fin 2, G.f₁ (γ₁ i) = G.f₂ (γ₂ i)) (i : Fin 2) :
    (G.γ₃ γ₁ γ₂ hγ i).1.1 = γ₁ i := rfl
@[scoped simp] theorem γ₃_snd (hγ : ∀ i : Fin 2, G.f₁ (γ₁ i) = G.f₂ (γ₂ i)) (i : Fin 2) :
    (G.γ₃ γ₁ γ₂ hγ i).1.2 = γ₂ i := rfl

theorem expand_fst (hγ : ∀ i : Fin 2, G.f₁ (γ₁ i) = G.f₂ (γ₂ i)) (c : Fin 2 → G.S3) (y : G.M3) :
    ((∑ i : Fin 2, WittVector.teichmuller p (c i) • G.γ₃ γ₁ γ₂ hγ i) + G.V3 y).1.1 =
      (∑ i : Fin 2, WittVector.teichmuller p ((c i).1.1) • γ₁ i) + G.D₁.verschiebung y.1.1 := by
  simp [Fin.sum_univ_two, WittVector.map_teichmuller]

theorem expand_snd (hγ : ∀ i : Fin 2, G.f₁ (γ₁ i) = G.f₂ (γ₂ i)) (c : Fin 2 → G.S3) (y : G.M3) :
    ((∑ i : Fin 2, WittVector.teichmuller p (c i) • G.γ₃ γ₁ γ₂ hγ i) + G.V3 y).1.2 =
      (∑ i : Fin 2, WittVector.teichmuller p ((c i).1.2) • γ₂ i) + G.D₂.verschiebung y.1.2 := by
  simp [Fin.sum_univ_two, WittVector.map_teichmuller]

theorem f₁_expand (c : Fin 2 → S₁) (y : G.D₁.M) :
    G.f₁ ((∑ i : Fin 2, WittVector.teichmuller p (c i) • γ₁ i) + G.D₁.verschiebung y) =
      (∑ i : Fin 2, WittVector.teichmuller p (G.q₁ (c i)) • G.f₁ (γ₁ i)) +
        G.D.verschiebung (G.f₁ y) := by
  simp [Fin.sum_univ_two, G.f₁_smul, WittVector.map_teichmuller, G.f₁_V]

theorem f₂_expand (hγ : ∀ i : Fin 2, G.f₁ (γ₁ i) = G.f₂ (γ₂ i)) (c : Fin 2 → S₂) (y : G.D₂.M) :
    G.f₂ ((∑ i : Fin 2, WittVector.teichmuller p (c i) • γ₂ i) + G.D₂.verschiebung y) =
      (∑ i : Fin 2, WittVector.teichmuller p (G.q₂ (c i)) • G.f₁ (γ₁ i)) +
        G.D.verschiebung (G.f₂ y) := by
  simp [Fin.sum_univ_two, G.f₂_smul, WittVector.map_teichmuller, G.f₂_V, hγ]

theorem isHomogeneousVBasis (hγ : ∀ i : Fin 2, G.f₁ (γ₁ i) = G.f₂ (γ₂ i))
    (hγ₁ : G.D₁.IsHomogeneousVBasis γ₁) (hγ₂ : G.D₂.IsHomogeneousVBasis γ₂)
    (hδ : G.D.IsHomogeneousVBasis (fun i => G.f₁ (γ₁ i))) :
    G.D3.IsHomogeneousVBasis (G.γ₃ γ₁ γ₂ hγ) := by
  refine ⟨fun i => ⟨hγ₁.1 i, hγ₂.1 i⟩, fun x => ?_⟩
  obtain ⟨⟨c₁, y₁⟩, h₁, -⟩ := hγ₁.2 x.1.1
  obtain ⟨⟨c₂, y₂⟩, h₂, -⟩ := hγ₂.2 x.1.2
  have e₁ : G.f₁ x.1.1 = (∑ i : Fin 2, WittVector.teichmuller p (G.q₁ (c₁ i)) • G.f₁ (γ₁ i)) +
      G.D.verschiebung (G.f₁ y₁) := by rw [h₁]; exact G.f₁_expand γ₁ c₁ y₁
  have e₂ : G.f₁ x.1.1 = (∑ i : Fin 2, WittVector.teichmuller p (G.q₂ (c₂ i)) • G.f₁ (γ₁ i)) +
      G.D.verschiebung (G.f₂ y₂) := by rw [G.rel x, h₂]; exact G.f₂_expand γ₁ γ₂ hγ c₂ y₂
  have hu := (hδ.2 (G.f₁ x.1.1)).unique (y₁ := (fun i => G.q₁ (c₁ i), G.f₁ y₁))
    (y₂ := (fun i => G.q₂ (c₂ i), G.f₂ y₂)) e₁ e₂
  have hc : ∀ i, G.q₁ (c₁ i) = G.q₂ (c₂ i) := fun i => congrFun (congrArg Prod.fst hu) i
  have hy : G.f₁ y₁ = G.f₂ y₂ := congrArg Prod.snd hu
  refine ⟨(fun i => ⟨(c₁ i, c₂ i), hc i⟩, ⟨(y₁, y₂), hy⟩), ?_, ?_⟩
  · show x = (∑ i : Fin 2, WittVector.teichmuller p _ • G.γ₃ γ₁ γ₂ hγ i) + G.V3 _
    apply G.ext3
    · rw [G.expand_fst γ₁ γ₂ hγ]; exact h₁
    · rw [G.expand_snd γ₁ γ₂ hγ]; exact h₂
  · rintro ⟨c', y'⟩ h'
    change x = (∑ i : Fin 2, WittVector.teichmuller p (c' i) • G.γ₃ γ₁ γ₂ hγ i) + G.V3 y' at h'
    have h₁' : x.1.1 = (∑ i : Fin 2, WittVector.teichmuller p ((c' i).1.1) • γ₁ i) +
        G.D₁.verschiebung y'.1.1 := by
      rw [← G.expand_fst γ₁ γ₂ hγ]; exact congrArg (fun z => z.1.1) h'
    have h₂' : x.1.2 = (∑ i : Fin 2, WittVector.teichmuller p ((c' i).1.2) • γ₂ i) +
        G.D₂.verschiebung y'.1.2 := by
      rw [← G.expand_snd γ₁ γ₂ hγ]; exact congrArg (fun z => z.1.2) h'
    have u₁ := (hγ₁.2 x.1.1).unique (y₁ := (fun i => (c' i).1.1, y'.1.1)) (y₂ := (c₁, y₁)) h₁' h₁
    have u₂ := (hγ₂.2 x.1.2).unique (y₁ := (fun i => (c' i).1.2, y'.1.2)) (y₂ := (c₂, y₂)) h₂' h₂
    have uc₁ : ∀ i, (c' i).1.1 = c₁ i := fun i => congrFun (congrArg Prod.fst u₁) i
    have uc₂ : ∀ i, (c' i).1.2 = c₂ i := fun i => congrFun (congrArg Prod.fst u₂) i
    refine Prod.ext ?_ ?_
    · funext i
      exact Subtype.ext (Prod.ext (uc₁ i) (uc₂ i))
    · have e1 : y'.1.1 = y₁ := by have := congrArg Prod.snd u₁; simpa using this
      have e2 : y'.1.2 = y₂ := by have := congrArg Prod.snd u₂; simpa using this
      exact G.ext3 e1 e2

end basis

theorem sum_iter_fst (x : ℕ → G.M3) (N : ℕ) (t : G.M3) :
    ((∑ m ∈ Finset.range N, (⇑G.V3)^[m] (x m)) + (⇑G.V3)^[N] t).1.1 =
      (∑ m ∈ Finset.range N, (⇑G.D₁.verschiebung)^[m] (x m).1.1) +
        (⇑G.D₁.verschiebung)^[N] t.1.1 := by
  have := map_add G.π₁ (∑ m ∈ Finset.range N, (⇑G.V3)^[m] (x m)) ((⇑G.V3)^[N] t)
  rw [map_sum] at this
  simp only [π₁_apply, G.π₁_iterV] at this
  exact this

theorem sum_iter_snd (x : ℕ → G.M3) (N : ℕ) (t : G.M3) :
    ((∑ m ∈ Finset.range N, (⇑G.V3)^[m] (x m)) + (⇑G.V3)^[N] t).1.2 =
      (∑ m ∈ Finset.range N, (⇑G.D₂.verschiebung)^[m] (x m).1.2) +
        (⇑G.D₂.verschiebung)^[N] t.1.2 := by
  have := map_add G.π₂ (∑ m ∈ Finset.range N, (⇑G.V3)^[m] (x m)) ((⇑G.V3)^[N] t)
  rw [map_sum] at this
  simp only [π₂_apply, G.π₂_iterV] at this
  exact this

theorem f₁_sum_iter (x : ℕ → G.D₁.M) (N : ℕ) (t : G.D₁.M) :
    G.f₁ ((∑ m ∈ Finset.range N, (⇑G.D₁.verschiebung)^[m] (x m)) + (⇑G.D₁.verschiebung)^[N] t) =
      (∑ m ∈ Finset.range N, (⇑G.D.verschiebung)^[m] (G.f₁ (x m))) +
        (⇑G.D.verschiebung)^[N] (G.f₁ t) := by
  rw [map_add, map_sum]; simp only [G.f₁_iterV]

theorem f₂_sum_iter (x : ℕ → G.D₂.M) (N : ℕ) (t : G.D₂.M) :
    G.f₂ ((∑ m ∈ Finset.range N, (⇑G.D₂.verschiebung)^[m] (x m)) + (⇑G.D₂.verschiebung)^[N] t) =
      (∑ m ∈ Finset.range N, (⇑G.D.verschiebung)^[m] (G.f₂ (x m))) +
        (⇑G.D.verschiebung)^[N] (G.f₂ t) := by
  rw [map_add, map_sum]; simp only [G.f₂_iterV]

theorem isVAdicallyComplete (hc₁ : G.D₁.IsVAdicallyComplete) (hc₂ : G.D₂.IsVAdicallyComplete)
    (hc : G.D.IsVAdicallyComplete) (hV : Function.Injective G.D.verschiebung) :
    G.D3.IsVAdicallyComplete := by
  intro x
  change ∃! s : G.M3, ∀ N : ℕ, ∃ t : G.M3,
    s = (∑ m ∈ Finset.range N, (⇑G.V3)^[m] (x m)) + (⇑G.V3)^[N] t
  obtain ⟨s₁, hs₁, us₁⟩ := hc₁ (fun m => (x m).1.1)
  obtain ⟨s₂, hs₂, us₂⟩ := hc₂ (fun m => (x m).1.2)
  have k₁ : ∀ N : ℕ, ∃ t : G.D.M, G.f₁ s₁ =
      (∑ m ∈ Finset.range N, (⇑G.D.verschiebung)^[m] (G.f₁ (x m).1.1)) +
        (⇑G.D.verschiebung)^[N] t := fun N => by
    obtain ⟨t, ht⟩ := hs₁ N
    exact ⟨G.f₁ t, by rw [ht]; exact G.f₁_sum_iter _ N t⟩
  have k₂ : ∀ N : ℕ, ∃ t : G.D.M, G.f₂ s₂ =
      (∑ m ∈ Finset.range N, (⇑G.D.verschiebung)^[m] (G.f₁ (x m).1.1)) +
        (⇑G.D.verschiebung)^[N] t := fun N => by
    obtain ⟨t, ht⟩ := hs₂ N
    refine ⟨G.f₂ t, ?_⟩
    rw [ht, G.f₂_sum_iter]
    congr 1
    exact Finset.sum_congr rfl fun m _ => by rw [G.rel (x m)]
  have hs : G.f₁ s₁ = G.f₂ s₂ := (hc _).unique k₁ k₂
  refine ⟨⟨(s₁, s₂), hs⟩, fun N => ?_, fun s' hs' => ?_⟩
  · obtain ⟨t₁, ht₁⟩ := hs₁ N
    obtain ⟨t₂, ht₂⟩ := hs₂ N
    have ht : G.f₁ t₁ = G.f₂ t₂ := by
      apply hV.iterate N
      have a₁ := congrArg G.f₁ ht₁
      rw [G.f₁_sum_iter] at a₁
      have a₂ := congrArg G.f₂ ht₂
      rw [G.f₂_sum_iter] at a₂
      have e : (∑ m ∈ Finset.range N, (⇑G.D.verschiebung)^[m] (G.f₂ (x m).1.2)) =
          ∑ m ∈ Finset.range N, (⇑G.D.verschiebung)^[m] (G.f₁ (x m).1.1) :=
        Finset.sum_congr rfl fun m _ => by rw [G.rel (x m)]
      rw [e, ← hs] at a₂
      exact add_left_cancel (a₁.symm.trans a₂)
    refine ⟨⟨(t₁, t₂), ht⟩, ?_⟩
    apply G.ext3
    · rw [G.sum_iter_fst]; exact ht₁
    · rw [G.sum_iter_snd]; exact ht₂
  · have h1 : s'.1.1 = s₁ := us₁ _ fun N => by
      obtain ⟨t, ht⟩ := hs' N
      exact ⟨t.1.1, by rw [← G.sum_iter_fst]; exact congrArg (fun z => z.1.1) ht⟩
    have h2 : s'.1.2 = s₂ := us₂ _ fun N => by
      obtain ⟨t, ht⟩ := hs' N
      exact ⟨t.1.2, by rw [← G.sum_iter_snd]; exact congrArg (fun z => z.1.2) ht⟩
    exact G.ext3 h1 h2

theorem isSpecial (hD : G.D.IsSpecialCartierModule) (hD₁ : G.D₁.IsSpecialCartierModule)
    (hD₂ : G.D₂.IsSpecialCartierModule)
    (γ₁ : Fin 2 → G.D₁.M) (γ₂ : Fin 2 → G.D₂.M) (hγ : ∀ i : Fin 2, G.f₁ (γ₁ i) = G.f₂ (γ₂ i))
    (hγ₁ : G.D₁.IsHomogeneousVBasis γ₁) (hγ₂ : G.D₂.IsHomogeneousVBasis γ₂)
    (hδ : G.D.IsHomogeneousVBasis (fun i => G.f₁ (γ₁ i))) :
    G.D3.IsSpecialCartierModule := by
  obtain ⟨⟨δ, hδ'⟩, hc⟩ := hD
  exact ⟨⟨G.γ₃ γ₁ γ₂ hγ, G.isHomogeneousVBasis γ₁ γ₂ hγ hγ₁ hγ₂ hδ⟩,
    G.isVAdicallyComplete hD₁.2 hD₂.2 hc hδ'.verschiebung_injective⟩

theorem isBaseChange₁ (γ₁ : Fin 2 → G.D₁.M) (γ₂ : Fin 2 → G.D₂.M)
    (hγ : ∀ i : Fin 2, G.f₁ (γ₁ i) = G.f₂ (γ₂ i))
    (hγ₁ : G.D₁.IsHomogeneousVBasis γ₁) (hγ₂ : G.D₂.IsHomogeneousVBasis γ₂)
    (hδ : G.D.IsHomogeneousVBasis (fun i => G.f₁ (γ₁ i))) :
    IsBaseChangeAlong' G.r₁ G.D3 G.D₁ G.π₁ :=
  ⟨fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ hx => hx.1,
    ⟨G.γ₃ γ₁ γ₂ hγ, G.isHomogeneousVBasis γ₁ γ₂ hγ hγ₁ hγ₂ hδ, hγ₁⟩⟩

theorem isBaseChange₂ (γ₁ : Fin 2 → G.D₁.M) (γ₂ : Fin 2 → G.D₂.M)
    (hγ : ∀ i : Fin 2, G.f₁ (γ₁ i) = G.f₂ (γ₂ i))
    (hγ₁ : G.D₁.IsHomogeneousVBasis γ₁) (hγ₂ : G.D₂.IsHomogeneousVBasis γ₂)
    (hδ : G.D.IsHomogeneousVBasis (fun i => G.f₁ (γ₁ i))) :
    IsBaseChangeAlong' G.r₂ G.D3 G.D₂ G.π₂ :=
  ⟨fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ hx => hx.2,
    ⟨G.γ₃ γ₁ γ₂ hγ, G.isHomogeneousVBasis γ₁ γ₂ hγ hγ₁ hγ₂ hδ, hγ₂⟩⟩

end Glue
p2m_reactivate "P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_dominating_of_apply_basis_eq.P2mAbsDom.Glue"

end P2mAbsDom
p2m_reactivate "P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_dominating_of_apply_basis_eq.P2mAbsDom.Glue P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_dominating_of_apply_basis_eq.P2mAbsDom"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_dominating_of_apply_basis_eq.P2mAbsDom.Glue P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_dominating_of_apply_basis_eq.P2mAbsDom"

theorem solution
    (p : ℕ) [Fact p.Prime] {B S₁ S₂ : Type} [CommRing B] [CommRing S₁] [CommRing S₂]
    (j : CerednikDrinfeld.Zp2 p →+* B)
    (j₁ : CerednikDrinfeld.Zp2 p →+* S₁) (j₂ : CerednikDrinfeld.Zp2 p →+* S₂)
    (q₁ : S₁ →+* B) (q₂ : S₂ →+* B) (hq₁ : q₁.comp j₁ = j) (hq₂ : q₂.comp j₂ = j)
    (hS₁ : ∀ s : S₁, (p : S₁) * s = 0 → s = 0) (hS₂ : ∀ s : S₂, (p : S₂) * s = 0 → s = 0)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (D₁ : CerednikDrinfeld.GradedCartierModuleData p S₁ j₁) (hD₁ : D₁.IsSpecialCartierModule)
    (D₂ : CerednikDrinfeld.GradedCartierModuleData p S₂ j₂) (hD₂ : D₂.IsSpecialCartierModule)
    (f₁ : D₁.M →+ D.M) (hf₁ : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' q₁ D₁ D f₁)
    (f₂ : D₂.M →+ D.M) (hf₂ : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' q₂ D₂ D f₂)
    (γ₁ : Fin 2 → D₁.M) (hγ₁ : D₁.IsHomogeneousVBasis γ₁)
    (γ₂ : Fin 2 → D₂.M) (hγ₂ : D₂.IsHomogeneousVBasis γ₂)
    (hγ : ∀ i : Fin 2, f₁ (γ₁ i) = f₂ (γ₂ i)) :
    ∃ (S₃ : Type) (_ : CommRing S₃) (j₃ : CerednikDrinfeld.Zp2 p →+* S₃) (r₁ : S₃ →+* S₁) (r₂ : S₃ →+* S₂)
      (_ : r₁.comp j₃ = j₁) (_ : r₂.comp j₃ = j₂) (_ : q₁.comp r₁ = q₂.comp r₂)
      (_ : ∀ s : S₃, (p : S₃) * s = 0 → s = 0)
      (D₃ : CerednikDrinfeld.GradedCartierModuleData p S₃ j₃) (_ : D₃.IsSpecialCartierModule)
      (γ₃ : Fin 2 → D₃.M) (_ : D₃.IsHomogeneousVBasis γ₃)
      (g₁ : D₃.M →+ D₁.M) (g₂ : D₃.M →+ D₂.M),
      CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' r₁ D₃ D₁ g₁ ∧
        CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' r₂ D₃ D₂ g₂ ∧
        (∀ i : Fin 2, g₁ (γ₃ i) = γ₁ i) ∧ (∀ i : Fin 2, g₂ (γ₃ i) = γ₂ i) ∧
        ∀ x : D₃.M, f₁ (g₁ x) = f₂ (g₂ x) := by
  let G : P2mAbsDom.Glue p B S₁ S₂ j j₁ j₂ :=
    { q₁ := q₁, q₂ := q₂, hq₁ := hq₁, hq₂ := hq₂, D := D, D₁ := D₁, D₂ := D₂, f₁ := f₁, f₂ := f₂,
      hf₁ := hf₁, hf₂ := hf₂ }
  have hδ : D.IsHomogeneousVBasis (fun i => f₁ (γ₁ i)) :=
    CerednikDrinfeld.GradedCartierModuleData.isHomogeneousVBasis_map_of_baseChange p q₁ D₁ hD₁ D hD
      f₁ hf₁ γ₁ hγ₁
  exact ⟨G.S3, inferInstance, G.j₃, G.r₁, G.r₂, G.r₁_comp_j₃, G.r₂_comp_j₃, G.q_comp_r,
    G.torsionFree hS₁ hS₂, G.D3, G.isSpecial hD hD₁ hD₂ γ₁ γ₂ hγ hγ₁ hγ₂ hδ, G.γ₃ γ₁ γ₂ hγ,
    G.isHomogeneousVBasis γ₁ γ₂ hγ hγ₁ hγ₂ hδ, G.π₁, G.π₂,
    G.isBaseChange₁ γ₁ γ₂ hγ hγ₁ hγ₂ hδ, G.isBaseChange₂ γ₁ γ₂ hγ hγ₁ hγ₂ hδ,
    fun _ => rfl, fun _ => rfl, fun x => x.2⟩

end S_CerednikDrinfeld_GradedCartierModuleData_exists_dominating_of_apply_basis_eq
end P2MW
export P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_dominating_of_apply_basis_eq (solution)
