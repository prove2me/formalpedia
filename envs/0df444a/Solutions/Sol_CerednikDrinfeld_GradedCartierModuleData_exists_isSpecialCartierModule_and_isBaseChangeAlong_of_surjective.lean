-- Prove2me | solution 1 for CerednikDrinfeld.GradedCartierModuleData.exists_isSpecialCartierModule_and_isBaseChangeAlong_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/95c6fb98-0323-5967-902b-046bec6a16d3

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_isSpecialCartierModule_and_isBaseChangeAlong_of_surjective

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Zp2 GradedCartierModuleData GradedCartierModuleData.IsBaseChangeAlong"
namespace GradedCartierModuleData
p2m_export "CerednikDrinfeld.GradedCartierModuleData" "IsHomogeneousVBasis IsVAdicallyComplete IsSpecialCartierModule IsBaseChangeAlong isCompl_piece varpi_varpi frobenius_smul varpi module frobenius_mem frobenius_verschiebung mk M verschiebung_mem verschiebung_smul_frobenius frobenius piece verschiebung varpi_mem smul_verschiebung varpi_verschiebung varpi_frobenius"
namespace SurjBaseChange
p2m_open "CerednikDrinfeld.GradedCartierModuleData CerednikDrinfeld"

p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_isSpecialCartierModule_and_isBaseChangeAlong_of_surjective.CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_isSpecialCartierModule_and_isBaseChangeAlong_of_surjective.CerednikDrinfeld.GradedCartierModuleData"

variable {p : ℕ} [Fact p.Prime] {B C : Type} [CommRing B] [CommRing C]

section Witt

variable (ψ : B →+* C)

def wKer : Ideal (WittVector p B) := RingHom.ker (WittVector.map (p := p) ψ)

theorem mem_wKer_iff (w : WittVector p B) : w ∈ wKer (p := p) ψ ↔ ∀ n, ψ (w.coeff n) = 0 := by
  rw [wKer, RingHom.mem_ker]
  constructor
  · intro h n
    have := congrArg (fun v : WittVector p C => v.coeff n) h
    simpa only [WittVector.map_coeff, WittVector.zero_coeff] using this
  · intro h
    ext n
    simp only [WittVector.map_coeff, WittVector.zero_coeff, h n]

theorem mem_wKer_iff' (w : WittVector p B) :
    w ∈ wKer (p := p) ψ ↔ WittVector.map (p := p) ψ w = 0 := Iff.rfl

theorem frobenius_mem_wKer {w : WittVector p B} (hw : w ∈ wKer (p := p) ψ) :
    WittVector.frobenius w ∈ wKer (p := p) ψ := by
  rw [mem_wKer_iff'] at hw ⊢
  have h : WittVector.map ψ (WittVector.frobenius w) =
      WittVector.frobenius (WittVector.map ψ w) :=
    WittVector.IsPoly.map (WittVector.frobenius_isPoly p) ψ w
  rw [h, hw, map_zero]

theorem teichmuller_mem_wKer {b : B} (hb : ψ b = 0) :
    WittVector.teichmuller p b ∈ wKer (p := p) ψ := by
  rw [mem_wKer_iff', WittVector.map_teichmuller, hb, WittVector.teichmuller_zero]

theorem exists_eq_verschiebung_of_coeff_zero (v : WittVector p B) (hv : v.coeff 0 = 0) :
    ∃ u : WittVector p B, v = WittVector.verschiebung u ∧ ∀ n, u.coeff n = v.coeff (n + 1) := by
  refine ⟨v.shift 1, ?_, fun n => by rw [WittVector.shift_coeff, add_comm]⟩
  have h := WittVector.eq_iterate_verschiebung (x := v) (n := 1) (fun i hi => by
    have : i = 0 := by omega
    subst this; exact hv)
  simpa using h

theorem coeff_zero_sub (x y : WittVector p B) : (x - y).coeff 0 = x.coeff 0 - y.coeff 0 := by
  have h := WittVector.add_coeff_zero (x - y) y
  rw [sub_add_cancel] at h
  rw [h]; ring

theorem exists_eq_teichmuller_add_verschiebung (w : WittVector p B) :
    ∃ w' : WittVector p B, w = WittVector.teichmuller p (w.coeff 0) + WittVector.verschiebung w' ∧
      (w ∈ wKer (p := p) ψ → w' ∈ wKer (p := p) ψ) := by
  set v := w - WittVector.teichmuller p (w.coeff 0) with hv
  have hv0 : v.coeff 0 = 0 := by
    rw [hv, coeff_zero_sub, WittVector.teichmuller_coeff_zero, sub_self]
  obtain ⟨u, hu, hucoeff⟩ := exists_eq_verschiebung_of_coeff_zero v hv0
  refine ⟨u, ?_, ?_⟩
  · rw [← hu, hv]; abel
  · intro hw
    have hvK : v ∈ wKer (p := p) ψ := by
      rw [hv]
      refine Ideal.sub_mem _ hw (teichmuller_mem_wKer ψ ?_)
      exact (mem_wKer_iff ψ w).1 hw 0
    rw [mem_wKer_iff] at hvK ⊢
    intro n
    rw [hucoeff]; exact hvK _

theorem exists_teichmuller_add_teichmuller (a b : B) (hb : ψ b = 0) :
    ∃ u ∈ wKer (p := p) ψ, WittVector.teichmuller p a + WittVector.teichmuller p b =
      WittVector.teichmuller p (a + b) + WittVector.verschiebung u := by
  set v := WittVector.teichmuller p a + WittVector.teichmuller p b - WittVector.teichmuller p (a + b)
    with hv
  have hv0 : v.coeff 0 = 0 := by
    rw [hv, coeff_zero_sub, WittVector.add_coeff_zero, WittVector.teichmuller_coeff_zero,
      WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero, sub_self]
  obtain ⟨u, hu, hucoeff⟩ := exists_eq_verschiebung_of_coeff_zero v hv0
  have hvK : v ∈ wKer (p := p) ψ := by
    rw [mem_wKer_iff', hv, map_sub, map_add, WittVector.map_teichmuller, WittVector.map_teichmuller,
      WittVector.map_teichmuller, map_add ψ, hb, add_zero, WittVector.teichmuller_zero, add_zero,
      sub_self]
  refine ⟨u, ?_, ?_⟩
  · rw [mem_wKer_iff] at hvK ⊢
    intro n; rw [hucoeff]; exact hvK _
  · rw [← hu, hv]; abel

theorem map_verschiebung' (w : WittVector p B) :
    WittVector.map ψ (WittVector.verschiebung w) = WittVector.verschiebung (WittVector.map ψ w) :=
  WittVector.map_verschiebung ψ w

theorem map_frobenius' (w : WittVector p B) :
    WittVector.map ψ (WittVector.frobenius w) = WittVector.frobenius (WittVector.map ψ w) :=
  WittVector.IsPoly.map (WittVector.frobenius_isPoly p) ψ w

end Witt

section Submodules

variable {j : Zp2 p →+* B} (ψ : B →+* C) (D : GradedCartierModuleData p B j)

def SJ : Submodule (WittVector p B) D.M := wKer (p := p) ψ • ⊤

def vImage (T : Submodule (WittVector p B) D.M) : Submodule (WittVector p B) D.M where
  carrier := D.verschiebung '' (T : Set D.M)
  zero_mem' := ⟨0, T.zero_mem, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, T.add_mem ha hb, map_add _ _ _⟩
  smul_mem' := by
    rintro w _ ⟨a, ha, rfl⟩
    exact ⟨WittVector.frobenius w • a, T.smul_mem _ ha, (D.smul_verschiebung w a).symm⟩

theorem mem_vImage_iff (T : Submodule (WittVector p B) D.M) (x : D.M) :
    x ∈ vImage D T ↔ ∃ t ∈ T, D.verschiebung t = x := by
  change x ∈ D.verschiebung '' (T : Set D.M) ↔ _
  simp only [Set.mem_image, SetLike.mem_coe]

theorem verschiebung_mem_vImage {T : Submodule (WittVector p B) D.M} {t : D.M} (ht : t ∈ T) :
    D.verschiebung t ∈ vImage D T :=
  (mem_vImage_iff D T _).2 ⟨t, ht, rfl⟩

theorem vImage_mono {T T' : Submodule (WittVector p B) D.M} (h : T ≤ T') : vImage D T ≤ vImage D T' := by
  intro x hx
  obtain ⟨t, ht, rfl⟩ := (mem_vImage_iff D T x).1 hx
  exact verschiebung_mem_vImage D (h ht)

def T : ℕ → Submodule (WittVector p B) D.M
  | 0 => ⊤
  | n + 1 => SJ ψ D ⊔ vImage D (T n)

theorem T_zero : T ψ D 0 = ⊤ := rfl

theorem T_succ (n : ℕ) : T ψ D (n + 1) = SJ ψ D ⊔ vImage D (T ψ D n) := rfl

def MJ (hψ : Function.Surjective ψ) : Submodule (WittVector p B) D.M := ⨅ n, T ψ D n

variable {ψ D}

theorem SJ_le_T (n : ℕ) : SJ ψ D ≤ T ψ D n := by
  cases n with
  | zero => exact le_top
  | succ n => rw [T_succ]; exact le_sup_left

theorem T_succ_le (n : ℕ) : T ψ D (n + 1) ≤ T ψ D n := by
  induction n with
  | zero => exact le_top
  | succ n ih =>
    rw [T_succ, T_succ]
    exact sup_le le_sup_left ((vImage_mono D ih).trans le_sup_right)

theorem T_antitone {m n : ℕ} (h : m ≤ n) : T ψ D n ≤ T ψ D m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact (T_succ_le _).trans ih

theorem verschiebung_mem_T_succ {n : ℕ} {t : D.M} (ht : t ∈ T ψ D n) :
    D.verschiebung t ∈ T ψ D (n + 1) := by
  rw [T_succ]; exact Submodule.mem_sup_right (verschiebung_mem_vImage D ht)

theorem mem_T_succ_iff {n : ℕ} {x : D.M} :
    x ∈ T ψ D (n + 1) ↔ ∃ s ∈ SJ ψ D, ∃ t ∈ T ψ D n, x = s + D.verschiebung t := by
  rw [T_succ, Submodule.mem_sup]
  constructor
  · rintro ⟨s, hs, v, hv, rfl⟩
    obtain ⟨t, ht, rfl⟩ := (mem_vImage_iff D _ v).1 hv
    exact ⟨s, hs, t, ht, rfl⟩
  · rintro ⟨s, hs, t, ht, rfl⟩
    exact ⟨s, hs, _, verschiebung_mem_vImage D ht, rfl⟩

theorem iterate_verschiebung_mem_T (n : ℕ) (t : D.M) : (⇑D.verschiebung)^[n] t ∈ T ψ D n := by
  induction n with
  | zero => exact Submodule.mem_top
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact verschiebung_mem_T_succ ih

variable {hψ : Function.Surjective ψ}

theorem mem_MJ_iff {x : D.M} : x ∈ MJ ψ D hψ ↔ ∀ n, x ∈ T ψ D n := Submodule.mem_iInf _

theorem MJ_le_T (n : ℕ) : MJ ψ D hψ ≤ T ψ D n := iInf_le _ n

theorem SJ_le_MJ : SJ ψ D ≤ MJ ψ D hψ := le_iInf fun n => SJ_le_T n

theorem smul_mem_SJ {w : WittVector p B} (hw : w ∈ wKer (p := p) ψ) (x : D.M) : w • x ∈ SJ ψ D :=
  Submodule.smul_mem_smul hw Submodule.mem_top

theorem smul_mem_MJ {w : WittVector p B} (hw : w ∈ wKer (p := p) ψ) (x : D.M) :
    w • x ∈ MJ ψ D hψ :=
  SJ_le_MJ (smul_mem_SJ hw x)

theorem verschiebung_mem_MJ {x : D.M} (hx : x ∈ MJ ψ D hψ) : D.verschiebung x ∈ MJ ψ D hψ := by
  rw [mem_MJ_iff] at hx ⊢
  intro n
  cases n with
  | zero => exact Submodule.mem_top
  | succ n => exact verschiebung_mem_T_succ (hx n)

theorem varpi_mem_SJ {x : D.M} (hx : x ∈ SJ ψ D) : D.varpi x ∈ SJ ψ D := by
  have h1 : D.varpi x ∈ (SJ ψ D).map D.varpi := Submodule.mem_map_of_mem hx
  have h2 : (SJ ψ D).map D.varpi ≤ SJ ψ D := by
    rw [SJ, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact h2 h1

theorem varpi_mem_T {n : ℕ} {x : D.M} (hx : x ∈ T ψ D n) : D.varpi x ∈ T ψ D n := by
  induction n generalizing x with
  | zero => exact Submodule.mem_top
  | succ n ih =>
    obtain ⟨s, hs, t, ht, rfl⟩ := mem_T_succ_iff.1 hx
    rw [map_add, D.varpi_verschiebung]
    exact mem_T_succ_iff.2 ⟨_, varpi_mem_SJ hs, _, ih ht, rfl⟩

theorem varpi_mem_MJ {x : D.M} (hx : x ∈ MJ ψ D hψ) : D.varpi x ∈ MJ ψ D hψ := by
  rw [mem_MJ_iff] at hx ⊢
  exact fun n => varpi_mem_T (hx n)

theorem frobenius_mem_SJ {x : D.M} (hx : x ∈ SJ ψ D) : D.frobenius x ∈ SJ ψ D := by
  refine Submodule.smul_induction_on (p := fun y => D.frobenius y ∈ SJ ψ D) hx ?_ ?_
  · intro w hw m _
    rw [D.frobenius_smul]
    exact smul_mem_SJ (frobenius_mem_wKer ψ hw) _
  · intro a b ha hb
    rw [map_add]; exact Submodule.add_mem _ ha hb

theorem frobenius_mem_T {n : ℕ} {x : D.M} (hx : x ∈ T ψ D (n + 1)) : D.frobenius x ∈ T ψ D n := by
  obtain ⟨s, hs, t, ht, rfl⟩ := mem_T_succ_iff.1 hx
  rw [map_add, D.frobenius_verschiebung]
  exact Submodule.add_mem _ (SJ_le_T n (frobenius_mem_SJ hs)) (Submodule.smul_of_tower_mem _ p ht)

theorem frobenius_mem_MJ {x : D.M} (hx : x ∈ MJ ψ D hψ) : D.frobenius x ∈ MJ ψ D hψ := by
  rw [mem_MJ_iff] at hx ⊢
  exact fun n => frobenius_mem_T (hx (n + 1))

theorem piece_decomp_unique {a₀ a₁ b₀ b₁ : D.M} (ha₀ : a₀ ∈ D.piece 0) (ha₁ : a₁ ∈ D.piece 1)
    (hb₀ : b₀ ∈ D.piece 0) (hb₁ : b₁ ∈ D.piece 1) (h : a₀ + a₁ = b₀ + b₁) : a₀ = b₀ ∧ a₁ = b₁ := by
  have hd := Submodule.disjoint_def.1 D.isCompl_piece.disjoint
  have h0 : a₀ - b₀ ∈ D.piece 0 := Submodule.sub_mem _ ha₀ hb₀
  have h1 : a₀ - b₀ ∈ D.piece 1 := by
    have : a₀ - b₀ = b₁ - a₁ := by
      rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
    rw [this]; exact Submodule.sub_mem _ hb₁ ha₁
  have := hd _ h0 h1
  constructor
  · exact sub_eq_zero.1 this
  · have h' : a₁ = b₀ + b₁ - a₀ := by rw [← h]; abel
    rw [h', sub_eq_zero.1 this]; abel

theorem exists_piece_decomp (x : D.M) :
    ∃ x₀ ∈ D.piece 0, ∃ x₁ ∈ D.piece 1, x = x₀ + x₁ := by
  have : x ∈ D.piece 0 ⊔ D.piece 1 := by
    rw [D.isCompl_piece.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 this
  exact ⟨y, hy, z, hz, rfl⟩

def IsGraded (S : Submodule (WittVector p B) D.M) : Prop :=
  ∀ x ∈ S, ∃ x₀ ∈ S, ∃ x₁ ∈ S, x₀ ∈ D.piece 0 ∧ x₁ ∈ D.piece 1 ∧ x = x₀ + x₁

theorem IsGraded.mem_of_decomp {S : Submodule (WittVector p B) D.M} (hS : IsGraded S) {x x₀ x₁ : D.M}
    (hx : x ∈ S) (h₀ : x₀ ∈ D.piece 0) (h₁ : x₁ ∈ D.piece 1) (h : x = x₀ + x₁) : x₀ ∈ S ∧ x₁ ∈ S := by
  obtain ⟨y₀, hy₀, y₁, hy₁, hy₀' , hy₁', rfl⟩ := hS x hx
  obtain ⟨rfl, rfl⟩ := piece_decomp_unique h₀ h₁ hy₀' hy₁' h.symm
  exact ⟨hy₀, hy₁⟩

theorem isGraded_top : IsGraded (D := D) ⊤ := by
  intro x _
  obtain ⟨x₀, h₀, x₁, h₁, rfl⟩ := exists_piece_decomp x
  exact ⟨x₀, Submodule.mem_top, x₁, Submodule.mem_top, h₀, h₁, rfl⟩

theorem isGraded_SJ : IsGraded (SJ ψ D) := by
  intro x hx
  refine Submodule.smul_induction_on
    (p := fun y => ∃ x₀ ∈ SJ ψ D, ∃ x₁ ∈ SJ ψ D, x₀ ∈ D.piece 0 ∧ x₁ ∈ D.piece 1 ∧ y = x₀ + x₁) hx ?_ ?_
  · intro w hw m _
    obtain ⟨m₀, h₀, m₁, h₁, rfl⟩ := exists_piece_decomp m
    refine ⟨w • m₀, smul_mem_SJ hw _, w • m₁, smul_mem_SJ hw _, Submodule.smul_mem _ _ h₀,
      Submodule.smul_mem _ _ h₁, smul_add _ _ _⟩
  · rintro a b ⟨a₀, ha₀, a₁, ha₁, ha₀', ha₁', rfl⟩ ⟨b₀, hb₀, b₁, hb₁, hb₀', hb₁', rfl⟩
    refine ⟨a₀ + b₀, Submodule.add_mem _ ha₀ hb₀, a₁ + b₁, Submodule.add_mem _ ha₁ hb₁,
      Submodule.add_mem _ ha₀' hb₀', Submodule.add_mem _ ha₁' hb₁', by abel⟩

theorem isGraded_vImage {S : Submodule (WittVector p B) D.M} (hS : IsGraded S) : IsGraded (vImage D S) := by
  intro x hx
  obtain ⟨t, ht, rfl⟩ := (mem_vImage_iff D S x).1 hx
  obtain ⟨t₀, ht₀, t₁, ht₁, h₀, h₁, rfl⟩ := hS t ht
  refine ⟨D.verschiebung t₁, verschiebung_mem_vImage D ht₁, D.verschiebung t₀,
    verschiebung_mem_vImage D ht₀, ?_, ?_, by rw [map_add, add_comm]⟩
  · have := D.verschiebung_mem 1 t₁ h₁
    simpa using this
  · have := D.verschiebung_mem 0 t₀ h₀
    simpa using this

theorem isGraded_sup {S S' : Submodule (WittVector p B) D.M} (hS : IsGraded S) (hS' : IsGraded S') :
    IsGraded (S ⊔ S') := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨a₀, ha₀, a₁, ha₁, ha₀', ha₁', rfl⟩ := hS a ha
  obtain ⟨b₀, hb₀, b₁, hb₁, hb₀', hb₁', rfl⟩ := hS' b hb
  refine ⟨a₀ + b₀, Submodule.add_mem _ (Submodule.mem_sup_left ha₀) (Submodule.mem_sup_right hb₀),
    a₁ + b₁, Submodule.add_mem _ (Submodule.mem_sup_left ha₁) (Submodule.mem_sup_right hb₁),
    Submodule.add_mem _ ha₀' hb₀', Submodule.add_mem _ ha₁' hb₁', by abel⟩

theorem isGraded_T (n : ℕ) : IsGraded (T ψ D n) := by
  induction n with
  | zero => exact isGraded_top
  | succ n ih => rw [T_succ]; exact isGraded_sup isGraded_SJ (isGraded_vImage ih)

theorem mem_MJ_of_decomp {x x₀ x₁ : D.M} (hx : x ∈ MJ ψ D hψ) (h₀ : x₀ ∈ D.piece 0)
    (h₁ : x₁ ∈ D.piece 1) (h : x = x₀ + x₁) : x₀ ∈ MJ ψ D hψ ∧ x₁ ∈ MJ ψ D hψ := by
  rw [mem_MJ_iff] at hx
  have key : ∀ n, x₀ ∈ T ψ D n ∧ x₁ ∈ T ψ D n := fun n =>
    (isGraded_T n).mem_of_decomp (hx n) h₀ h₁ h
  exact ⟨mem_MJ_iff.2 fun n => (key n).1, mem_MJ_iff.2 fun n => (key n).2⟩

theorem SJ_digits {γ : Fin 2 → D.M} (hγ : D.IsHomogeneousVBasis γ) {s : D.M} (hs : s ∈ SJ ψ D) :
    ∃ a : Fin 2 → B, (∀ i, ψ (a i) = 0) ∧ ∃ s' ∈ SJ ψ D,
      s = (∑ i : Fin 2, WittVector.teichmuller p (a i) • γ i) + D.verschiebung s' := by
  refine Submodule.smul_induction_on
    (p := fun y => ∃ a : Fin 2 → B, (∀ i, ψ (a i) = 0) ∧ ∃ s' ∈ SJ ψ D,
      y = (∑ i : Fin 2, WittVector.teichmuller p (a i) • γ i) + D.verschiebung s') hs ?_ ?_
  · intro w hw m _

    obtain ⟨⟨c, y⟩, hcy, -⟩ := hγ.2 m
    obtain ⟨w', hw', hw'K⟩ := exists_eq_teichmuller_add_verschiebung (p := p) ψ w
    have hw0 : ψ (w.coeff 0) = 0 := (mem_wKer_iff ψ w).1 hw 0
    have hw'K := hw'K hw
    refine ⟨fun i => w.coeff 0 * c i, fun i => by rw [map_mul, hw0, zero_mul], ?_⟩
    refine ⟨WittVector.frobenius (WittVector.teichmuller p (w.coeff 0)) • y + w' • D.frobenius m,
      Submodule.add_mem _ (smul_mem_SJ (frobenius_mem_wKer ψ (teichmuller_mem_wKer ψ hw0)) _)
        (smul_mem_SJ hw'K _), ?_⟩

    have e1 : w • m = WittVector.teichmuller p (w.coeff 0) • m + D.verschiebung (w' • D.frobenius m) := by
      conv_lhs => rw [hw']
      rw [add_smul, D.verschiebung_smul_frobenius]
    have e2 : WittVector.teichmuller p (w.coeff 0) • m =
        (∑ i : Fin 2, WittVector.teichmuller p (w.coeff 0 * c i) • γ i) +
          D.verschiebung (WittVector.frobenius (WittVector.teichmuller p (w.coeff 0)) • y) := by
      conv_lhs => rw [hcy]
      rw [smul_add, Finset.smul_sum, D.smul_verschiebung]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_smul, ← map_mul (WittVector.teichmuller p)]
    rw [e1, e2, map_add, add_assoc]
  · rintro x y ⟨a, ha, s, hs, rfl⟩ ⟨b, hb, t, ht, rfl⟩

    have hu : ∀ i, ∃ u ∈ wKer (p := p) ψ, WittVector.teichmuller p (a i) + WittVector.teichmuller p (b i) =
        WittVector.teichmuller p (a i + b i) + WittVector.verschiebung u :=
      fun i => exists_teichmuller_add_teichmuller ψ (a i) (b i) (hb i)
    choose u hu huE using hu
    refine ⟨fun i => a i + b i, fun i => by rw [map_add, ha, hb, add_zero], ?_⟩
    refine ⟨s + t + ∑ i : Fin 2, u i • D.frobenius (γ i),
      Submodule.add_mem _ (Submodule.add_mem _ hs ht)
        (Submodule.sum_mem _ fun i _ => smul_mem_SJ (hu i) _), ?_⟩
    have key : ∀ i, WittVector.teichmuller p (a i) • γ i + WittVector.teichmuller p (b i) • γ i =
        WittVector.teichmuller p (a i + b i) • γ i + D.verschiebung (u i • D.frobenius (γ i)) := by
      intro i
      rw [← add_smul, huE, add_smul, D.verschiebung_smul_frobenius]
    have e1 : (∑ i : Fin 2, WittVector.teichmuller p (a i) • γ i) +
        (∑ i : Fin 2, WittVector.teichmuller p (b i) • γ i) =
        (∑ i : Fin 2, WittVector.teichmuller p (a i + b i) • γ i) +
          D.verschiebung (∑ i : Fin 2, u i • D.frobenius (γ i)) := by
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib,
        map_sum]
    calc _ = ((∑ i : Fin 2, WittVector.teichmuller p (a i) • γ i) +
          (∑ i : Fin 2, WittVector.teichmuller p (b i) • γ i)) + (D.verschiebung s + D.verschiebung t) := by
          abel
      _ = _ := by rw [e1, map_add, map_add]; abel

theorem MJ_digits {γ : Fin 2 → D.M} (hγ : D.IsHomogeneousVBasis γ) {x : D.M} (hx : x ∈ MJ ψ D hψ) :
    ∃ a : Fin 2 → B, (∀ i, ψ (a i) = 0) ∧ ∃ y ∈ MJ ψ D hψ,
      x = (∑ i : Fin 2, WittVector.teichmuller p (a i) • γ i) + D.verschiebung y := by
  rw [mem_MJ_iff] at hx

  have dec : ∀ n, ∃ a : Fin 2 → B, (∀ i, ψ (a i) = 0) ∧ ∃ y ∈ T ψ D n,
      x = (∑ i : Fin 2, WittVector.teichmuller p (a i) • γ i) + D.verschiebung y := by
    intro n
    obtain ⟨s, hs, t, ht, hx'⟩ := mem_T_succ_iff.1 (hx (n + 1))
    obtain ⟨a, ha, s', hs', rfl⟩ := SJ_digits hγ hs
    refine ⟨a, ha, s' + t, Submodule.add_mem _ (SJ_le_T n hs') ht, ?_⟩
    rw [hx', map_add]; abel
  obtain ⟨a, ha, y, hy0, hxy⟩ := dec 0
  refine ⟨a, ha, y, ?_, hxy⟩
  rw [mem_MJ_iff]
  intro n
  obtain ⟨a', ha', y', hy', hxy'⟩ := dec n

  have huniq := (hγ.2 x).unique (y₁ := (a, y)) (y₂ := (a', y')) hxy hxy'
  have : y = y' := congrArg Prod.snd huniq
  rw [this]; exact hy'

theorem digits_unique_mod_MJ {γ : Fin 2 → D.M} (hγ : D.IsHomogeneousVBasis γ)
    (b b' : Fin 2 → B) (y y' : D.M)
    (h : ((∑ i : Fin 2, WittVector.teichmuller p (b i) • γ i) + D.verschiebung y) -
      ((∑ i : Fin 2, WittVector.teichmuller p (b' i) • γ i) + D.verschiebung y') ∈ MJ ψ D hψ) :
    (∀ i, ψ (b i) = ψ (b' i)) ∧ y - y' ∈ MJ ψ D hψ := by
  obtain ⟨a, ha, m, hm, hd⟩ := MJ_digits hγ h

  have hu : ∀ i, ∃ u ∈ wKer (p := p) ψ, WittVector.teichmuller p (b' i) + WittVector.teichmuller p (a i) =
      WittVector.teichmuller p (b' i + a i) + WittVector.verschiebung u :=
    fun i => exists_teichmuller_add_teichmuller ψ (b' i) (a i) (ha i)
  choose u hu huE using hu

  have hx : (∑ i : Fin 2, WittVector.teichmuller p (b i) • γ i) + D.verschiebung y =
      (∑ i : Fin 2, WittVector.teichmuller p (b' i + a i) • γ i) +
        D.verschiebung (y' + m + ∑ i : Fin 2, u i • D.frobenius (γ i)) := by
    have e := sub_eq_iff_eq_add.1 hd
    rw [e]
    have key : ∀ i, WittVector.teichmuller p (b' i) • γ i + WittVector.teichmuller p (a i) • γ i =
        WittVector.teichmuller p (b' i + a i) • γ i + D.verschiebung (u i • D.frobenius (γ i)) := by
      intro i
      rw [← add_smul, huE, add_smul, D.verschiebung_smul_frobenius]
    have e1 : (∑ i : Fin 2, WittVector.teichmuller p (b' i) • γ i) +
        (∑ i : Fin 2, WittVector.teichmuller p (a i) • γ i) =
        (∑ i : Fin 2, WittVector.teichmuller p (b' i + a i) • γ i) +
          D.verschiebung (∑ i : Fin 2, u i • D.frobenius (γ i)) := by
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib,
        map_sum]
    calc _ = ((∑ i : Fin 2, WittVector.teichmuller p (b' i) • γ i) +
          (∑ i : Fin 2, WittVector.teichmuller p (a i) • γ i)) + (D.verschiebung m + D.verschiebung y') := by
          abel
      _ = _ := by rw [e1, map_add, map_add]; abel
  have huniq := (hγ.2 _).unique (y₁ := (b, y))
    (y₂ := (fun i => b' i + a i, y' + m + ∑ i : Fin 2, u i • D.frobenius (γ i))) rfl hx
  have hb : b = fun i => b' i + a i := congrArg Prod.fst huniq
  have hy : y = y' + m + ∑ i : Fin 2, u i • D.frobenius (γ i) := congrArg Prod.snd huniq
  constructor
  · intro i
    rw [show b i = b' i + a i from congrFun hb i, map_add, ha, add_zero]
  · rw [hy, show y' + m + (∑ i : Fin 2, u i • D.frobenius (γ i)) - y' =
        m + ∑ i : Fin 2, u i • D.frobenius (γ i) by abel]
    exact Submodule.add_mem _ hm (Submodule.sum_mem _ fun i _ => smul_mem_MJ (hu i) _)

end Submodules

section Quotient

variable {j : Zp2 p →+* B} (ψ : B →+* C) (hψ : Function.Surjective ψ)
  (D : GradedCartierModuleData p B j)

include hψ

abbrev Q : Type := D.M ⧸ MJ ψ D hψ

theorem wmap_surjective : Function.Surjective (WittVector.map (p := p) ψ) :=
  WittVector.map_surjective ψ hψ

scoped instance instSMulQ : SMul (WittVector p C) (Q ψ hψ D) :=
  ⟨fun c x => Function.surjInv (wmap_surjective (p := p) ψ hψ) c • x⟩

theorem smulQ_def (c : WittVector p C) (x : Q ψ hψ D) :
    c • x = Function.surjInv (wmap_surjective (p := p) ψ hψ) c • x := rfl

theorem wKer_smul {w : WittVector p B} (hw : w ∈ wKer (p := p) ψ) (x : Q ψ hψ D) : w • x = 0 := by
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective (MJ ψ D hψ) x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact smul_mem_MJ hw m

theorem map_smul_eq (w : WittVector p B) (x : Q ψ hψ D) : (WittVector.map ψ w) • x = w • x := by
  rw [smulQ_def]
  set w' := Function.surjInv (wmap_surjective (p := p) ψ hψ) (WittVector.map ψ w) with hw'def
  have hw' : WittVector.map ψ w' = WittVector.map ψ w := Function.surjInv_eq _ _
  have hk : w' - w ∈ wKer (p := p) ψ := by rw [mem_wKer_iff', map_sub, hw', sub_self]
  calc w' • x = (w' - w) • x + w • x := by rw [sub_smul, sub_add_cancel]
    _ = w • x := by rw [wKer_smul ψ hψ D hk, zero_add]

scoped instance instModuleQ : Module (WittVector p C) (Q ψ hψ D) :=
  Function.Surjective.moduleLeft (WittVector.map (p := p) ψ) (wmap_surjective (p := p) ψ hψ)
    (map_smul_eq ψ hψ D)

theorem teichmuller_smul_mk (b : B) (m : D.M) :
    WittVector.teichmuller p (ψ b) • (Submodule.Quotient.mk m : Q ψ hψ D) =
      Submodule.Quotient.mk (WittVector.teichmuller p b • m) := by
  rw [← WittVector.map_teichmuller, map_smul_eq, Submodule.Quotient.mk_smul]

theorem mk_sum {ι : Type} (s : Finset ι) (f : ι → D.M) :
    (Submodule.Quotient.mk (∑ i ∈ s, f i) : Q ψ hψ D) =
      ∑ i ∈ s, (Submodule.Quotient.mk (f i) : Q ψ hψ D) :=
  map_sum (MJ ψ D hψ).mkQ f s

theorem mk_sum_teichmuller (b : Fin 2 → B) (γ : Fin 2 → D.M) :
    (Submodule.Quotient.mk (∑ i : Fin 2, WittVector.teichmuller p (b i) • γ i) : Q ψ hψ D) =
      ∑ i : Fin 2, WittVector.teichmuller p (ψ (b i)) • (Submodule.Quotient.mk (γ i) : Q ψ hψ D) := by
  rw [mk_sum]
  exact Finset.sum_congr rfl fun i _ => (teichmuller_smul_mk ψ hψ D (b i) (γ i)).symm

def frobQ : Q ψ hψ D →+ Q ψ hψ D :=
  QuotientAddGroup.map (MJ ψ D hψ).toAddSubgroup (MJ ψ D hψ).toAddSubgroup D.frobenius
    (fun x hx => frobenius_mem_MJ (hψ := hψ) hx)

theorem frobQ_mk (m : D.M) :
    frobQ ψ hψ D (Submodule.Quotient.mk m) = Submodule.Quotient.mk (D.frobenius m) := rfl

def verQ : Q ψ hψ D →+ Q ψ hψ D :=
  QuotientAddGroup.map (MJ ψ D hψ).toAddSubgroup (MJ ψ D hψ).toAddSubgroup D.verschiebung
    (fun x hx => verschiebung_mem_MJ (hψ := hψ) hx)

theorem verQ_mk (m : D.M) :
    verQ ψ hψ D (Submodule.Quotient.mk m) = Submodule.Quotient.mk (D.verschiebung m) := rfl

def varpiQB : Q ψ hψ D →ₗ[WittVector p B] Q ψ hψ D :=
  (MJ ψ D hψ).mapQ (MJ ψ D hψ) D.varpi (fun x hx => varpi_mem_MJ (hψ := hψ) hx)

theorem varpiQB_mk (m : D.M) :
    varpiQB ψ hψ D (Submodule.Quotient.mk m) = Submodule.Quotient.mk (D.varpi m) := rfl

def varpiQ : Q ψ hψ D →ₗ[WittVector p C] Q ψ hψ D where
  toFun := varpiQB ψ hψ D
  map_add' := map_add _
  map_smul' c x := by
    show varpiQB ψ hψ D (Function.surjInv (wmap_surjective (p := p) ψ hψ) c • x) =
      Function.surjInv (wmap_surjective (p := p) ψ hψ) c • varpiQB ψ hψ D x
    exact map_smul _ _ _

theorem varpiQ_mk (m : D.M) :
    varpiQ ψ hψ D (Submodule.Quotient.mk m) = Submodule.Quotient.mk (D.varpi m) := rfl

def pieceQ (i : Fin 2) : Submodule (WittVector p C) (Q ψ hψ D) where
  carrier := {x | ∃ m ∈ D.piece i, Submodule.Quotient.mk m = x}
  zero_mem' := ⟨0, Submodule.zero_mem _, rfl⟩
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, Submodule.add_mem _ ha hb, rfl⟩
  smul_mem' := by
    rintro c _ ⟨a, ha, rfl⟩
    exact ⟨Function.surjInv (wmap_surjective (p := p) ψ hψ) c • a, Submodule.smul_mem _ _ ha, rfl⟩

theorem mem_pieceQ_iff (i : Fin 2) (x : Q ψ hψ D) :
    x ∈ pieceQ ψ hψ D i ↔ ∃ m ∈ D.piece i, Submodule.Quotient.mk m = x := Iff.rfl

theorem mk_mem_pieceQ {i : Fin 2} {m : D.M} (hm : m ∈ D.piece i) :
    (Submodule.Quotient.mk m : Q ψ hψ D) ∈ pieceQ ψ hψ D i := ⟨m, hm, rfl⟩

def quot : GradedCartierModuleData p C (ψ.comp j) where
  M := Q ψ hψ D
  frobenius := frobQ ψ hψ D
  verschiebung := verQ ψ hψ D
  varpi := varpiQ ψ hψ D
  piece := pieceQ ψ hψ D
  frobenius_smul := by
    intro c x
    obtain ⟨w, rfl⟩ := wmap_surjective (p := p) ψ hψ c
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective (MJ ψ D hψ) x
    rw [map_smul_eq, ← Submodule.Quotient.mk_smul, frobQ_mk, frobQ_mk, D.frobenius_smul,
      Submodule.Quotient.mk_smul, ← map_smul_eq ψ hψ D, map_frobenius']
  smul_verschiebung := by
    intro c x
    obtain ⟨w, rfl⟩ := wmap_surjective (p := p) ψ hψ c
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective (MJ ψ D hψ) x
    rw [map_smul_eq, verQ_mk, ← Submodule.Quotient.mk_smul, D.smul_verschiebung, ← verQ_mk,
      Submodule.Quotient.mk_smul, ← map_smul_eq ψ hψ D, map_frobenius']
  verschiebung_smul_frobenius := by
    intro c x
    obtain ⟨w, rfl⟩ := wmap_surjective (p := p) ψ hψ c
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective (MJ ψ D hψ) x
    rw [map_smul_eq, frobQ_mk, ← Submodule.Quotient.mk_smul, verQ_mk, D.verschiebung_smul_frobenius,
      Submodule.Quotient.mk_smul, ← map_smul_eq ψ hψ D, map_verschiebung']
  frobenius_verschiebung := by
    intro x
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective (MJ ψ D hψ) x
    rw [verQ_mk, frobQ_mk, D.frobenius_verschiebung]
    exact map_nsmul (MJ ψ D hψ).mkQ p m
  varpi_verschiebung := by
    intro x
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective (MJ ψ D hψ) x
    rw [verQ_mk, varpiQ_mk, varpiQ_mk, verQ_mk, D.varpi_verschiebung]
  varpi_frobenius := by
    intro x
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective (MJ ψ D hψ) x
    rw [frobQ_mk, varpiQ_mk, varpiQ_mk, frobQ_mk, D.varpi_frobenius]
  varpi_varpi := by
    intro x
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective (MJ ψ D hψ) x
    rw [varpiQ_mk, varpiQ_mk, D.varpi_varpi]
    exact map_nsmul (MJ ψ D hψ).mkQ p m
  isCompl_piece := by
    refine IsCompl.of_eq ?_ ?_
    · rw [Submodule.eq_bot_iff]
      rintro x ⟨⟨m₀, hm₀, rfl⟩, ⟨m₁, hm₁, he⟩⟩
      have hd : m₁ - m₀ ∈ MJ ψ D hψ := (Submodule.Quotient.eq _).1 he
      have key := mem_MJ_of_decomp hd (x₀ := -m₀) (x₁ := m₁) (Submodule.neg_mem _ hm₀) hm₁ (by abel)
      rw [Submodule.Quotient.mk_eq_zero]
      exact (Submodule.neg_mem_iff _).1 key.1
    · rw [Submodule.eq_top_iff']
      intro x
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective (MJ ψ D hψ) x
      obtain ⟨m₀, h₀, m₁, h₁, rfl⟩ := exists_piece_decomp (D := D) m
      rw [Submodule.Quotient.mk_add]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (mk_mem_pieceQ ψ hψ D h₀))
        (Submodule.mem_sup_right (mk_mem_pieceQ ψ hψ D h₁))
  verschiebung_mem := by
    rintro i x ⟨m, hm, rfl⟩
    exact ⟨D.verschiebung m, D.verschiebung_mem i m hm, (verQ_mk ψ hψ D m).symm⟩
  frobenius_mem := by
    rintro i x ⟨m, hm, rfl⟩
    exact ⟨D.frobenius m, D.frobenius_mem i m hm, (frobQ_mk ψ hψ D m).symm⟩
  varpi_mem := by
    rintro i x ⟨m, hm, rfl⟩
    exact ⟨D.varpi m, D.varpi_mem i m hm, (varpiQ_mk ψ hψ D m).symm⟩

theorem quot_M : (quot ψ hψ D).M = Q ψ hψ D := rfl

def proj : D.M →+ (quot ψ hψ D).M := (MJ ψ D hψ).mkQ.toAddMonoidHom

theorem proj_apply (m : D.M) : proj ψ hψ D m = (Submodule.Quotient.mk m : Q ψ hψ D) := rfl

theorem proj_surjective : Function.Surjective (proj ψ hψ D) :=
  Submodule.Quotient.mk_surjective (MJ ψ D hψ)

theorem quot_verschiebung_mk (m : D.M) :
    (quot ψ hψ D).verschiebung (Submodule.Quotient.mk m) = Submodule.Quotient.mk (D.verschiebung m) := rfl

theorem quot_isHomogeneousVBasis {γ : Fin 2 → D.M} (hγ : D.IsHomogeneousVBasis γ) :
    (quot ψ hψ D).IsHomogeneousVBasis (fun i => proj ψ hψ D (γ i)) := by
  refine ⟨fun i => mk_mem_pieceQ ψ hψ D (hγ.1 i), fun x => ?_⟩
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective (MJ ψ D hψ) x
  obtain ⟨⟨b, y⟩, hby, -⟩ := hγ.2 m

  have hexp : ∀ (b' : Fin 2 → B) (y' : D.M),
      (Submodule.Quotient.mk ((∑ i : Fin 2, WittVector.teichmuller p (b' i) • γ i) + D.verschiebung y') :
        Q ψ hψ D) =
      (∑ i : Fin 2, WittVector.teichmuller p (ψ (b' i)) • proj ψ hψ D (γ i)) +
        (quot ψ hψ D).verschiebung (Submodule.Quotient.mk y') := by
    intro b' y'
    rw [Submodule.Quotient.mk_add, mk_sum_teichmuller]
    rfl
  refine ⟨(fun i => ψ (b i), (Submodule.Quotient.mk y : Q ψ hψ D)), ?_, ?_⟩
  · show (Submodule.Quotient.mk m : Q ψ hψ D) =
      (∑ i : Fin 2, WittVector.teichmuller p (ψ (b i)) • proj ψ hψ D (γ i)) +
        (quot ψ hψ D).verschiebung (Submodule.Quotient.mk y)
    rw [← hexp, ← hby]
  · rintro ⟨c, q⟩ hcq

    have hb' : ∀ i, ∃ b' : B, ψ b' = c i := fun i => hψ (c i)
    choose b' hb' using hb'
    obtain ⟨y', rfl⟩ := Submodule.Quotient.mk_surjective (MJ ψ D hψ) q
    have hcq' : (Submodule.Quotient.mk m : Q ψ hψ D) =
        Submodule.Quotient.mk ((∑ i : Fin 2, WittVector.teichmuller p (b' i) • γ i) + D.verschiebung y') := by
      rw [hexp]
      simp only [hb']
      exact hcq
    rw [hby] at hcq'
    have hmem := (Submodule.Quotient.eq _).1 hcq'
    obtain ⟨hdig, hrem⟩ := digits_unique_mod_MJ (hψ := hψ) hγ b b' y y' hmem
    refine Prod.ext ?_ ?_
    · funext i
      show c i = ψ (b i)
      rw [← hb', hdig]
    · show (Submodule.Quotient.mk y' : Q ψ hψ D) = Submodule.Quotient.mk y
      exact ((Submodule.Quotient.eq _).2 hrem).symm

theorem mk_iterate_verschiebung (n : ℕ) (m : D.M) :
    (Submodule.Quotient.mk ((⇑D.verschiebung)^[n] m) : Q ψ hψ D) =
      (⇑(quot ψ hψ D).verschiebung)^[n] (Submodule.Quotient.mk m) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    rfl

theorem quot_isVAdicallyComplete (hD : D.IsVAdicallyComplete) : (quot ψ hψ D).IsVAdicallyComplete := by
  intro x
  have hlift : ∀ n, ∃ ξ : D.M, (Submodule.Quotient.mk ξ : Q ψ hψ D) = x n :=
    fun n => Submodule.Quotient.mk_surjective (MJ ψ D hψ) (x n)
  choose ξ hξ using hlift
  obtain ⟨s, hs, -⟩ := hD ξ

  have hsum : ∀ N : ℕ, (Submodule.Quotient.mk (∑ m ∈ Finset.range N, (⇑D.verschiebung)^[m] (ξ m)) :
      Q ψ hψ D) = ∑ m ∈ Finset.range N, (⇑(quot ψ hψ D).verschiebung)^[m] (x m) := by
    intro N
    rw [mk_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [mk_iterate_verschiebung, hξ]
  refine ⟨(Submodule.Quotient.mk s : Q ψ hψ D), ?_, ?_⟩
  · intro N
    obtain ⟨t, ht⟩ := hs N
    refine ⟨Submodule.Quotient.mk t, ?_⟩
    show (Submodule.Quotient.mk s : Q ψ hψ D) =
      (∑ m ∈ Finset.range N, (⇑(quot ψ hψ D).verschiebung)^[m] (x m)) +
        (⇑(quot ψ hψ D).verschiebung)^[N] (Submodule.Quotient.mk t)
    rw [ht, Submodule.Quotient.mk_add, hsum, mk_iterate_verschiebung]
    rfl
  · intro s' hs'
    obtain ⟨σ, rfl⟩ := Submodule.Quotient.mk_surjective (MJ ψ D hψ) s'
    apply (Submodule.Quotient.eq _).2
    rw [mem_MJ_iff]
    intro N
    obtain ⟨t, ht⟩ := hs N
    obtain ⟨t', ht'⟩ := hs' N
    obtain ⟨τ, rfl⟩ := Submodule.Quotient.mk_surjective (MJ ψ D hψ) t'
    have e1 : (Submodule.Quotient.mk (σ - s) : Q ψ hψ D) =
        Submodule.Quotient.mk ((⇑D.verschiebung)^[N] τ - (⇑D.verschiebung)^[N] t) := by
      rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub, mk_iterate_verschiebung,
        mk_iterate_verschiebung]
      have hs0 : (Submodule.Quotient.mk s : Q ψ hψ D) =
          (∑ m ∈ Finset.range N, (⇑(quot ψ hψ D).verschiebung)^[m] (x m)) +
            (⇑(quot ψ hψ D).verschiebung)^[N] (Submodule.Quotient.mk t) := by
        rw [ht, Submodule.Quotient.mk_add, hsum, mk_iterate_verschiebung]
        rfl
      rw [hs0]
      change (Submodule.Quotient.mk σ : Q ψ hψ D) - _ = _
      rw [ht']
      abel
    have hmem : (σ - s) - ((⇑D.verschiebung)^[N] τ - (⇑D.verschiebung)^[N] t) ∈ MJ ψ D hψ :=
      (Submodule.Quotient.eq _).1 e1
    have : σ - s = ((σ - s) - ((⇑D.verschiebung)^[N] τ - (⇑D.verschiebung)^[N] t)) +
        ((⇑D.verschiebung)^[N] τ - (⇑D.verschiebung)^[N] t) := by abel
    rw [this]
    exact Submodule.add_mem _ (MJ_le_T N hmem)
      (Submodule.sub_mem _ (iterate_verschiebung_mem_T N τ) (iterate_verschiebung_mem_T N t))

theorem quot_isSpecialCartierModule (hD : D.IsSpecialCartierModule) :
    (quot ψ hψ D).IsSpecialCartierModule := by
  obtain ⟨⟨γ, hγ⟩, hc⟩ := hD
  exact ⟨⟨_, quot_isHomogeneousVBasis ψ hψ D hγ⟩, quot_isVAdicallyComplete ψ hψ D hc⟩

theorem proj_isBaseChangeAlong (hD : D.IsSpecialCartierModule) :
    IsBaseChangeAlong ψ D (quot ψ hψ D) (proj ψ hψ D) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w x
    show (Submodule.Quotient.mk (w • x) : Q ψ hψ D) = WittVector.map ψ w • Submodule.Quotient.mk x
    rw [Submodule.Quotient.mk_smul]
    exact (map_smul_eq ψ hψ D w _).symm
  · intro x; rfl
  · intro x; rfl
  · intro x; rfl
  · intro i x hx; exact mk_mem_pieceQ ψ hψ D hx
  · obtain ⟨γ, hγ⟩ := hD.1
    exact ⟨γ, hγ, quot_isHomogeneousVBasis ψ hψ D hγ⟩

end Quotient

end CerednikDrinfeld.GradedCartierModuleData.SurjBaseChange
p2m_reactivate "P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_isSpecialCartierModule_and_isBaseChangeAlong_of_surjective.CerednikDrinfeld P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_isSpecialCartierModule_and_isBaseChangeAlong_of_surjective.CerednikDrinfeld.GradedCartierModuleData P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_isSpecialCartierModule_and_isBaseChangeAlong_of_surjective.CerednikDrinfeld.GradedCartierModuleData.SurjBaseChange"
p2m_reactivate "P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_isSpecialCartierModule_and_isBaseChangeAlong_of_surjective.CerednikDrinfeld P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_isSpecialCartierModule_and_isBaseChangeAlong_of_surjective.CerednikDrinfeld.GradedCartierModuleData"
p2m_reactivate "P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_isSpecialCartierModule_and_isBaseChangeAlong_of_surjective.CerednikDrinfeld"

open _root_.CerednikDrinfeld _root_.P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_isSpecialCartierModule_and_isBaseChangeAlong_of_surjective.CerednikDrinfeld _root_.CerednikDrinfeld.GradedCartierModuleData _root_.P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_isSpecialCartierModule_and_isBaseChangeAlong_of_surjective.CerednikDrinfeld.GradedCartierModuleData CerednikDrinfeld.GradedCartierModuleData.SurjBaseChange in

theorem solution
    (p : ℕ) [Fact p.Prime] {B C : Type} [CommRing B] [CommRing C]
    (j : CerednikDrinfeld.Zp2 p →+* B) (ψ : B →+* C) (hψ : Function.Surjective ψ)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule) :
    ∃ (D₁ : CerednikDrinfeld.GradedCartierModuleData p C (ψ.comp j)) (g : D.M →+ D₁.M),
      D₁.IsSpecialCartierModule ∧
      CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong ψ D D₁ g ∧
      ∀ γ : Fin 2 → D.M, D.IsHomogeneousVBasis γ → D₁.IsHomogeneousVBasis (fun i => g (γ i)) :=
  ⟨quot ψ hψ D, proj ψ hψ D, quot_isSpecialCartierModule ψ hψ D hD, proj_isBaseChangeAlong ψ hψ D hD,
    fun _ hγ => quot_isHomogeneousVBasis ψ hψ D hγ⟩

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_isSpecialCartierModule_and_isBaseChangeAlong_of_surjective.CerednikDrinfeld P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_isSpecialCartierModule_and_isBaseChangeAlong_of_surjective.CerednikDrinfeld.GradedCartierModuleData P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_isSpecialCartierModule_and_isBaseChangeAlong_of_surjective.CerednikDrinfeld.GradedCartierModuleData.SurjBaseChange"

end S_CerednikDrinfeld_GradedCartierModuleData_exists_isSpecialCartierModule_and_isBaseChangeAlong_of_surjective
end P2MW
export P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_isSpecialCartierModule_and_isBaseChangeAlong_of_surjective (solution)
