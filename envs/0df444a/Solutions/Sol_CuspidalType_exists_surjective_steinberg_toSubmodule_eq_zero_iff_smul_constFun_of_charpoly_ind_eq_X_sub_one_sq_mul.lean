-- Prove2me | solution 1 for CuspidalType.exists_surjective_steinberg_toSubmodule_eq_zero_iff_smul_constFun_of_charpoly_ind_eq_X_sub_one_sq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/21e74374-a869-533f-9426-69ba6ae4481d

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Theorems.Thm_BrauerNesbitt_exists_linearEquiv_of_span_range_eq_top_of_trace_eq
import Theorems.Thm_Representation_span_range_eq_top_of_isIrreducible
import Theorems.Thm_Representation_span_range_eq_top_of_span_range_eq_top_of_trace_eq
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspidalType_exists_surjective_steinberg_toSubmodule_eq_zero_iff_smul_constFun_of_charpoly_ind_eq_X_sub_one_sq_mul

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Polynomial Matrix
open CuspidalType
open scoped TensorProduct

namespace SteinbergQuotAux

section trace

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

theorem trace_prod_eq {A B : Type*} [AddCommGroup A] [Module k A] [FiniteDimensional k A]
    [AddCommGroup B] [Module k B] [FiniteDimensional k B] (F : (A × B) →ₗ[k] (A × B)) :
    LinearMap.trace k (A × B) F =
      LinearMap.trace k A (LinearMap.fst k A B ∘ₗ F ∘ₗ LinearMap.inl k A B) +
        LinearMap.trace k B (LinearMap.snd k A B ∘ₗ F ∘ₗ LinearMap.inr k A B) := by
  have hF : F = F ∘ₗ (LinearMap.inl k A B ∘ₗ LinearMap.fst k A B) +
      F ∘ₗ (LinearMap.inr k A B ∘ₗ LinearMap.snd k A B) := by
    rw [← LinearMap.comp_add]
    apply LinearMap.ext
    rintro ⟨a, b⟩
    simp
  conv_lhs => rw [hF]
  rw [map_add, ← LinearMap.comp_assoc, LinearMap.trace_comp_comm',
    ← LinearMap.comp_assoc (LinearMap.snd k A B) (LinearMap.inr k A B) F,
    LinearMap.trace_comp_comm' (LinearMap.snd k A B)]

theorem trace_eq_trace_restrict_add_trace_quotient (f : V →ₗ[k] V) (W : Submodule k V)
    (hW : W ≤ W.comap f) :
    LinearMap.trace k V f =
      LinearMap.trace k W (f.restrict (fun _ hx => hW hx)) +
        LinearMap.trace k (V ⧸ W) (W.mapQ W f hW) := by
  obtain ⟨W', hc⟩ := W.exists_isCompl
  set e : (W × W') ≃ₗ[k] V := Submodule.prodEquivOfIsCompl W W' hc with he
  have h1 : LinearMap.trace k V f = LinearMap.trace k (W × W') (e.symm.conj f) := by
    rw [LinearMap.trace_conj']
  rw [h1, trace_prod_eq]
  congr 1
  · congr 1
    apply LinearMap.ext
    intro w
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.inl_apply, LinearEquiv.conj_apply,
      LinearEquiv.symm_symm, LinearMap.fst_apply, LinearEquiv.coe_coe]
    have hfw : f w ∈ W := hW w.2
    have : e.symm (f (e (w, 0))) = (⟨f w, hfw⟩, 0) := by
      rw [LinearEquiv.symm_apply_eq]
      simp [e, Submodule.coe_prodEquivOfIsCompl']
    rw [this]
    rfl
  · set eq : (V ⧸ W) ≃ₗ[k] W' := Submodule.quotientEquivOfIsCompl W W' hc with heq
    rw [← LinearMap.trace_conj' (W.mapQ W f hW) eq]
    congr 1
    apply LinearMap.ext
    intro w'
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.inr_apply, LinearEquiv.conj_apply,
      LinearEquiv.symm_symm, LinearMap.snd_apply, LinearEquiv.coe_coe]
    obtain ⟨a, b, hab⟩ : ∃ a : W, ∃ b : W', f (w' : V) = a + b := by
      have : f (w' : V) ∈ W ⊔ W' := by rw [hc.sup_eq_top]; trivial
      obtain ⟨a, ha, b, hb, h⟩ := Submodule.mem_sup.mp this
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, h.symm⟩
    have h2 : e.symm (f (e (0, w'))) = (a, b) := by
      rw [LinearEquiv.symm_apply_eq]
      simp [e, Submodule.coe_prodEquivOfIsCompl', hab]
    rw [h2]
    change b = eq (W.mapQ W f hW (eq.symm w'))
    rw [heq, Submodule.quotientEquivOfIsCompl_symm_apply, Submodule.mapQ_apply, hab]
    apply Subtype.ext
    rw [Submodule.Quotient.mk_add, map_add, Submodule.quotientEquivOfIsCompl_apply_mk_right,
      (Submodule.Quotient.mk_eq_zero W).mpr a.2, map_zero, zero_add]

theorem trace_eq_finrank_add_trace_quotient (f : V →ₗ[k] V) (W : Submodule k V)
    (hW : ∀ w ∈ W, f w = w) :
    LinearMap.trace k V f =
      Module.finrank k W + LinearMap.trace k (V ⧸ W) (W.mapQ W f (fun w hw => by
        rw [Submodule.mem_comap, hW w hw]; exact hw)) := by
  have hle : W ≤ W.comap f := fun w hw => by rw [Submodule.mem_comap, hW w hw]; exact hw
  rw [trace_eq_trace_restrict_add_trace_quotient f W hle]
  congr 1
  have hid : (f.restrict (fun _ hx => hle hx) : W →ₗ[k] W) = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨w, hw⟩
    exact Subtype.ext (hW w hw)
  rw [hid, LinearMap.trace_id]

theorem trace_eq_trace_restrict_add_finrank (f : V →ₗ[k] V) (W : Submodule k V)
    (hW : W ≤ W.comap f) (hq : ∀ v, f v - v ∈ W) :
    LinearMap.trace k V f =
      LinearMap.trace k W (f.restrict (fun _ hx => hW hx)) + Module.finrank k (V ⧸ W) := by
  rw [trace_eq_trace_restrict_add_trace_quotient f W hW]
  congr 1
  have hid : W.mapQ W f hW = LinearMap.id := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x => rw [Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.eq]; exact hq x
  rw [hid, LinearMap.trace_id]

end trace

section model

p2m_open "Module Matrix.Module"

theorem exists_of_span_eq_top {k : Type} [Field k] {G : Type} [Group G]
    {N : Type} [AddCommGroup N] [Module k N] [FiniteDimensional k N]
    (ind : Representation k G N) (St : Submodule k N) (hSt : ∀ g, ∀ v ∈ St, ind g v ∈ St)
    (σ : N →ₗ[k] k) (hσSt : ∀ v, v ∈ St ↔ σ v = 0) (hσ : ∀ g v, σ (ind g v) = σ v)
    (hσs : Function.Surjective σ)
    (c : N) (hc0 : c ≠ 0) (hcSt : c ∈ St) (hindc : ∀ g, ind g c = c)
    {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (ρ : Representation k G V)
    (hspan : Submodule.span k (Set.range ⇑ρ) = ⊤)
    (htr : ∀ g, LinearMap.trace k N (ind g) = LinearMap.trace k V (ρ g) + 2)
    (hfin : finrank k N = finrank k V + 2) :
    ∃ π : St →ₗ[k] V, (∀ (g : G) (v : St), π ⟨ind g v, hSt g v v.2⟩ = ρ g (π v)) ∧
      Function.Surjective π ∧ ∀ v : St, π v = 0 ↔ ∃ t : k, (v : N) = t • c := by
  classical
  set C : Submodule k N := k ∙ c with hC
  have hCle : C ≤ St := by
    rw [hC, Submodule.span_le, Set.singleton_subset_iff]; exact hcSt
  have hCN : ∀ g, C ≤ C.comap (ind g) := by
    intro g
    rw [hC, Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Submodule.mem_comap, hindc]
    exact Submodule.mem_span_singleton_self _
  have hCid : ∀ g, ∀ w ∈ C, ind g w = w := by
    intro g w hw
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_smul, hindc]
  set indQ : Representation k G (N ⧸ C) := ind.quotient C hCN with hindQ

  have hCker : C ≤ LinearMap.ker σ := fun w hw => (hσSt w).mp (hCle hw)
  set τ : (N ⧸ C) →ₗ[k] k := C.liftQ σ hCker with hτ
  have hτmk : ∀ v : N, τ (C.mkQ v) = σ v := fun v => rfl
  have hτind : ∀ g x, τ (indQ g x) = τ x := by
    intro g x
    induction x using Submodule.Quotient.induction_on with
    | H v => exact hσ g v
  have hτsurj : Function.Surjective τ := by
    intro t
    obtain ⟨v, hv⟩ := hσs t
    exact ⟨C.mkQ v, by rw [hτmk, hv]⟩
  set L : Submodule k (N ⧸ C) := LinearMap.ker τ with hL
  have hLst : ∀ g, ∀ x ∈ L, indQ g x ∈ L := by
    intro g x hx
    rw [hL, LinearMap.mem_ker] at hx ⊢
    rw [hτind, hx]
  set Lsub : Subrepresentation indQ := ⟨L, fun g x hx => hLst g x hx⟩ with hLsub
  set lam : Representation k G L := Lsub.toRepresentation with hlam
  have hmkL : ∀ v : St, C.mkQ (v : N) ∈ L := by
    intro v
    rw [hL, LinearMap.mem_ker, hτmk]
    exact (hσSt v).mp v.2

  have hfinC : finrank k C = 1 := finrank_span_singleton hc0
  have hfinNC : finrank k (N ⧸ C) + 1 = finrank k N := by
    have := Submodule.finrank_quotient_add_finrank C
    rw [hfinC] at this
    exact this
  have hfinL : finrank k L + 1 = finrank k (N ⧸ C) := by
    have h := LinearMap.finrank_range_add_finrank_ker τ
    rw [LinearMap.range_eq_top.mpr hτsurj, finrank_top, Module.finrank_self, add_comm] at h
    rw [hL]; exact h
  have hfinL' : finrank k V = finrank k L := by omega

  have htr1 : ∀ g, LinearMap.trace k N (ind g) = 1 + LinearMap.trace k (N ⧸ C) (indQ g) := by
    intro g
    rw [trace_eq_finrank_add_trace_quotient (ind g) C (hCid g), hfinC, Nat.cast_one]
    rfl
  have htr2 : ∀ g, LinearMap.trace k (N ⧸ C) (indQ g) = LinearMap.trace k L (lam g) + 1 := by
    intro g
    rw [trace_eq_trace_restrict_add_finrank (indQ g) L (fun x hx => hLst g x hx) (fun x => by
      rw [hL, LinearMap.mem_ker, map_sub, hτind, sub_self])]
    have : finrank k ((N ⧸ C) ⧸ L) = 1 := by
      have h1 := Submodule.finrank_quotient_add_finrank L
      omega
    rw [this, Nat.cast_one]
    rfl
  have htr' : ∀ g, LinearMap.trace k V (ρ g) = LinearMap.trace k L (lam g) := by
    intro g
    have h1 := htr g
    rw [htr1, htr2] at h1
    linear_combination -h1

  have hspanL : Submodule.span k (Set.range ⇑lam) = ⊤ :=
    Representation.span_range_eq_top_of_span_range_eq_top_of_trace_eq ρ lam hfinL' hspan htr'
  obtain ⟨e, he⟩ :=
    BrauerNesbitt.exists_linearEquiv_of_span_range_eq_top_of_trace_eq ρ lam hspan hspanL htr'
  have he' : ∀ g y, e.symm (lam g y) = ρ g (e.symm y) := by
    intro g y
    rw [LinearEquiv.symm_apply_eq, he, LinearEquiv.apply_symm_apply]

  set θ : St →ₗ[k] L := LinearMap.codRestrict L (C.mkQ ∘ₗ St.subtype) hmkL with hθ
  refine ⟨e.symm.toLinearMap ∘ₗ θ, ?_, ?_, ?_⟩
  · intro g v
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, ← he' g]
    congr 1
  · refine e.symm.surjective.comp ?_
    rintro ⟨x, hx⟩
    induction x using Submodule.Quotient.induction_on with
    | H v =>
      have hv : v ∈ St := by
        rw [hL, LinearMap.mem_ker, ← Submodule.mkQ_apply, hτmk] at hx
        exact (hσSt v).mpr hx
      exact ⟨⟨v, hv⟩, rfl⟩
  · intro v
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff, hθ,
      ← Subtype.coe_inj, LinearMap.codRestrict_apply, Submodule.coe_zero, LinearMap.comp_apply,
      Submodule.subtype_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hC,
      Submodule.mem_span_singleton]
    exact ⟨fun ⟨t, ht⟩ => ⟨t, ht.symm⟩, fun ⟨t, ht⟩ => ⟨t, ht.symm⟩⟩

end model

section charpolyRel

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {V' : Type*} [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']

private theorem _root_.SteinbergQuotAux.trace_eq_neg_charpoly_nextCoeff (f : V →ₗ[k] V) :
    LinearMap.trace k V f = -f.charpoly.nextCoeff := by
  classical
  rw [LinearMap.trace_eq_matrix_trace k (Module.Free.chooseBasis k V),
    Matrix.trace_eq_neg_charpoly_nextCoeff, LinearMap.charpoly_toMatrix]

p2m_export "SteinbergQuotAux" "trace_eq_neg_charpoly_nextCoeff"

theorem finrank_eq_of_charpoly_eq (f : V →ₗ[k] V) (f' : V' →ₗ[k] V')
    (h : f'.charpoly = (X - 1) ^ 2 * f.charpoly) :
    Module.finrank k V' = Module.finrank k V + 2 := by
  rw [show (X - 1 : k[X]) = X - C 1 by rw [C_1]] at h
  have := congrArg natDegree h
  rw [natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero 1)) (LinearMap.charpoly_monic f).ne_zero,
    natDegree_pow, natDegree_X_sub_C, LinearMap.charpoly_natDegree,
    LinearMap.charpoly_natDegree] at this
  omega

theorem trace_eq_of_charpoly_eq (f : V →ₗ[k] V) (f' : V' →ₗ[k] V')
    (h : f'.charpoly = (X - 1) ^ 2 * f.charpoly) :
    LinearMap.trace k V' f' = LinearMap.trace k V f + 2 := by
  rw [show (X - 1 : k[X]) = X - C 1 by rw [C_1]] at h
  rw [trace_eq_neg_charpoly_nextCoeff, trace_eq_neg_charpoly_nextCoeff, h,
    Monic.nextCoeff_mul ((monic_X_sub_C 1).pow 2) (LinearMap.charpoly_monic f),
    Monic.nextCoeff_pow (monic_X_sub_C 1), nextCoeff_X_sub_C]
  ring

end charpolyRel

section key

variable {K : Type*} [Field K] [IsAlgClosed K] {M : Type*} [AddCommGroup M] [Module K M]
  [FiniteDimensional K M]

theorem sub_one_le_finrank_of_stable (q : ℕ) [hq : Fact q.Prime]
    (u : M →ₗ[K] M) (d : (ZMod q)ˣ → (M →ₗ[K] M)) (huq : u ^ q = 1)
    (hdu : ∀ a : (ZMod q)ˣ, u ∘ₗ d a = d a ∘ₗ (u ^ (a : ZMod q).val))
    (hdinj : ∀ a, Function.Injective (d a))
    (W : Submodule K M) (hWu : ∀ w ∈ W, u w ∈ W) (hWd : ∀ a, ∀ w ∈ W, d a w ∈ W)
    (hW0 : W ≠ ⊥) (hfix : ∀ w ∈ W, u w = w → w = 0) :
    q - 1 ≤ Module.finrank K W := by
  classical
  haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW0
  set uW : Module.End K W := u.restrict hWu with huW

  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue uW
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  have hw0 : (w : M) ≠ 0 := fun h => hw.2 (Subtype.ext h)
  have huw : u w = μ • (w : M) := by
    have := hw.apply_eq_smul
    rw [huW] at this
    exact congrArg Subtype.val this

  have hupow : ∀ n : ℕ, (u ^ n) w = μ ^ n • (w : M) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, huw, smul_smul, pow_succ, mul_comm]
  have hμq : μ ^ q = 1 := by
    have := hupow q
    rw [huq, Module.End.one_apply] at this
    have h2 : (μ ^ q - 1) • (w : M) = 0 := by rw [sub_smul, one_smul, ← this, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hw0
  have hμ1 : μ ≠ 1 := by
    intro h
    rw [h, one_smul] at huw
    exact hw0 (hfix w w.2 huw)
  have hprim : IsPrimitiveRoot μ q := by
    have := orderOf_eq_prime (p := q) hμq hμ1
    rw [← this]; exact IsPrimitiveRoot.orderOf μ

  have hind : iSupIndep fun a : (ZMod q)ˣ => uW.eigenspace (μ ^ (a : ZMod q).val) := by
    refine (Module.End.eigenspaces_iSupIndep uW).comp ?_
    intro a b hab
    simp only at hab
    have := hprim.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hab
    exact Units.ext (ZMod.val_injective q this)
  have hne : ∀ a : (ZMod q)ˣ, uW.eigenspace (μ ^ (a : ZMod q).val) ≠ ⊥ := by
    intro a
    rw [Submodule.ne_bot_iff]
    refine ⟨⟨d a w, hWd a w w.2⟩, ?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      apply Subtype.ext
      change u (d a w) = ((μ ^ (a : ZMod q).val) • (⟨d a w, hWd a w w.2⟩ : W) : W)
      rw [Submodule.coe_smul]
      have := LinearMap.congr_fun (hdu a) w
      simp only [LinearMap.coe_comp, Function.comp_apply] at this
      rw [this, hupow, map_smul]
    · intro h
      have h' : d a w = 0 := congrArg Subtype.val h
      exact hw0 (hdinj a (by rw [h', map_zero]))
  haveI : Fintype {a : (ZMod q)ˣ // uW.eigenspace (μ ^ (a : ZMod q).val) ≠ ⊥} := Fintype.ofFinite _
  have hle := hind.subtype_ne_bot_le_finrank
  have hcard : Fintype.card {a : (ZMod q)ˣ // uW.eigenspace (μ ^ (a : ZMod q).val) ≠ ⊥} = q - 1 := by
    rw [Fintype.card_of_subtype (Finset.univ) (fun a => by simp [hne a]), Finset.card_univ,
      ZMod.card_units]
  rw [hcard] at hle
  exact hle

end key

section descent

variable {κ : Type*} [Field κ] (K : Type*) [Field K] [Algebra κ K]
  {V : Type*} [AddCommGroup V] [Module κ V] [FiniteDimensional κ V]

theorem eq_top_of_span_baseChange_eq_top (S : Submodule κ (V →ₗ[κ] V))
    (h : Submodule.span K ((fun f : V →ₗ[κ] V => f.baseChange K) '' (S : Set (V →ₗ[κ] V))) =
      (⊤ : Submodule K (K ⊗[κ] V →ₗ[K] K ⊗[κ] V))) :
    S = ⊤ := by

  set g : S →ₗ[κ] (K ⊗[κ] V →ₗ[K] K ⊗[κ] V) :=
    ((LinearMap.baseChangeHom κ K V V).restrictScalars κ) ∘ₗ S.subtype with hg
  set Ψ : K ⊗[κ] S →ₗ[K] (K ⊗[κ] V →ₗ[K] K ⊗[κ] V) := g.liftBaseChange K with hΨ
  have hrange : (⊤ : Submodule K (K ⊗[κ] V →ₗ[K] K ⊗[κ] V)) ≤ LinearMap.range Ψ := by
    rw [← h, Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    refine ⟨(1 : K) ⊗ₜ ⟨f, hf⟩, ?_⟩
    rw [hΨ, LinearMap.liftBaseChange_tmul, one_smul]
    rfl
  have h1 : Module.finrank K (K ⊗[κ] V →ₗ[K] K ⊗[κ] V) ≤ Module.finrank κ S := by
    calc Module.finrank K (K ⊗[κ] V →ₗ[K] K ⊗[κ] V)
        = Module.finrank K (⊤ : Submodule K (K ⊗[κ] V →ₗ[K] K ⊗[κ] V)) := (finrank_top K _).symm
      _ ≤ Module.finrank K (LinearMap.range Ψ) := Submodule.finrank_mono hrange
      _ ≤ Module.finrank K (K ⊗[κ] S) := LinearMap.finrank_range_le Ψ
      _ = Module.finrank κ S := Module.finrank_baseChange
  have h2 : Module.finrank K (K ⊗[κ] V →ₗ[K] K ⊗[κ] V) = Module.finrank κ (V →ₗ[κ] V) := by
    rw [Module.finrank_linearMap, Module.finrank_linearMap, Module.finrank_baseChange]
  apply Submodule.eq_top_of_finrank_eq
  apply le_antisymm (Submodule.finrank_le S)
  rw [← h2]; exact h1

end descent

section cyclic

variable {k : Type*} [Field k] {G : Type*} [Group G] {S : Type*} [MulAction G S] [Finite S]

theorem minimalPeriod_eq_natCard (g : G) (htrans : ∀ x y : S, ∃ n : ℕ, g ^ n • x = y) (x : S) :
    Function.minimalPeriod (fun y => g • y) x = Nat.card S := by
  classical
  haveI : Fintype S := Fintype.ofFinite S
  have hall : ∀ y : S, y ∈ MulAction.orbit (Subgroup.zpowers g) x := by
    intro y
    obtain ⟨n, hn⟩ := htrans x y
    exact ⟨⟨g ^ n, Subgroup.npow_mem_zpowers g n⟩, hn⟩
  rw [MulAction.minimalPeriod_eq_card, ← Nat.card_eq_fintype_card,
    Nat.card_congr (Equiv.subtypeUnivEquiv hall)]

theorem pow_natCard_smul (g : G) (htrans : ∀ x y : S, ∃ n : ℕ, g ^ n • x = y) (x : S) :
    g ^ Nat.card S • x = x := by
  rw [MulAction.pow_smul_eq_iff_minimalPeriod_dvd, minimalPeriod_eq_natCard g htrans x]

theorem pow_smul_injOn (g : G) (htrans : ∀ x y : S, ∃ n : ℕ, g ^ n • x = y) (x : S)
    {i j : ℕ} (hi : i < Nat.card S) (hj : j < Nat.card S) (h : g ^ i • x = g ^ j • x) : i = j := by
  have key : ∀ n : ℕ, g ^ n • x = x ↔ Nat.card S ∣ n := fun n => by
    rw [MulAction.pow_smul_eq_iff_minimalPeriod_dvd, minimalPeriod_eq_natCard g htrans x]
  wlog hij : i ≤ j generalizing i j
  · exact (this hj hi h.symm (le_of_not_ge hij)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  have : g ^ d • x = x := by
    have h2 : g ^ (i + d) • x = g ^ i • (g ^ d • x) := by rw [← mul_smul, ← pow_add]
    rw [h2] at h
    exact (smul_left_cancel_iff (g ^ i)).mp h.symm
  rw [key] at this
  have hd : d = 0 := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · exact hd
    · exact absurd (Nat.le_of_dvd hd this) (by omega)
  simp [hd]

variable (k) in

theorem charpoly_lmapDomain_of_transitive [Nonempty S] (g : G)
    (htrans : ∀ x y : S, ∃ n : ℕ, g ^ n • x = y) :
    (Finsupp.lmapDomain k k (fun y : S => g • y)).charpoly = X ^ Nat.card S - 1 := by
  classical
  haveI : Fintype S := Fintype.ofFinite S
  set f : (S →₀ k) →ₗ[k] (S →₀ k) := Finsupp.lmapDomain k k (fun y : S => g • y) with hf
  set n := Nat.card S with hn
  have hnpos : 0 < n := by rw [hn]; exact Nat.card_pos

  have hfpow : ∀ m : ℕ, f ^ m = Finsupp.lmapDomain k k (fun y : S => g ^ m • y) := by
    intro m
    induction m with
    | zero =>
      ext x
      simp [f, Finsupp.lmapDomain_apply]
    | succ m ih =>
      rw [pow_succ, ih]
      apply LinearMap.ext
      intro l
      rw [Module.End.mul_apply, Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply,
        Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp]
      congr 1
      ext y
      simp only [Function.comp_apply, smul_smul, ← pow_succ]
  have hfn : f ^ n = 1 := by
    rw [hfpow]
    apply LinearMap.ext
    intro l
    rw [Finsupp.lmapDomain_apply, Module.End.one_apply]
    conv_rhs => rw [← Finsupp.mapDomain_id (v := l)]
    congr 1
    ext y
    exact pow_natCard_smul g htrans y

  have hXn1 : (X ^ n - 1 : k[X]) = X ^ n - C 1 := by rw [C_1]
  have hXn : (X ^ n - 1 : k[X]).Monic := by rw [hXn1]; exact monic_X_pow_sub_C (1 : k) hnpos.ne'
  have hdvd1 : minpoly k f ∣ X ^ n - 1 := by
    apply minpoly.dvd
    simp [hfn]

  have hmonic : (minpoly k f).Monic := minpoly.monic (LinearMap.isIntegral f)
  have hdeg : n ≤ (minpoly k f).natDegree := by
    by_contra hlt
    push Not at hlt
    obtain ⟨x⟩ := ‹Nonempty S›
    have h0 : (Polynomial.aeval f (minpoly k f)) (Finsupp.single x 1) = 0 :=
      LinearMap.congr_fun (minpoly.aeval k f) (Finsupp.single x 1)
    rw [hmonic.as_sum, map_add, map_sum] at h0
    simp only [map_pow, aeval_X, map_mul, aeval_C, LinearMap.add_apply, LinearMap.coe_sum,
      Finset.sum_apply, Module.End.mul_apply, Module.algebraMap_end_apply] at h0
    have h1 : ∀ i : ℕ, (f ^ i) (Finsupp.single x 1) = Finsupp.single (g ^ i • x) 1 := by
      intro i
      rw [hfpow, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    simp only [h1, Finsupp.smul_single, smul_eq_mul, mul_one] at h0
    have h2 := congrArg (fun l : S →₀ k => l (g ^ (minpoly k f).natDegree • x)) h0
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, Finsupp.coe_finsetSum,
      Finset.sum_apply, Finsupp.coe_zero, Pi.zero_apply] at h2
    rw [Finset.sum_eq_zero, add_zero] at h2
    · exact one_ne_zero h2
    · intro i hi
      rw [Finset.mem_range] at hi
      rw [Finsupp.single_eq_of_ne]
      intro heq
      have := pow_smul_injOn g htrans x hlt (hi.trans hlt) heq
      omega

  have hmin : minpoly k f = X ^ n - 1 := by
    refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmonic hXn hdvd1 ?_).symm
    rw [hXn1, natDegree_X_pow_sub_C]; exact hdeg
  have hchar : f.charpoly = minpoly k f := by
    refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmonic (LinearMap.charpoly_monic f)
      (LinearMap.minpoly_dvd_charpoly f) ?_
    rw [LinearMap.charpoly_natDegree, Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card]
    exact hdeg
  rw [hchar, hmin]

end cyclic

variable (q : ℕ) [hq : Fact q.Prime]

theorem mulVec_ne_zero (A : GL2 q) (v : Fin 2 → ZMod q) (hv : v ≠ 0) :
    (A : Matrix (Fin 2) (Fin 2) (ZMod q)) *ᵥ v ≠ 0 := by
  intro h
  apply hv
  have := congrArg (fun w => ((A⁻¹ : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) *ᵥ w) h
  simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
  rwa [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one,
    Matrix.one_mulVec] at this

private theorem _root_.SteinbergQuotAux.smul_mk (A : GL2 q) (v : Fin 2 → ZMod q) (hv : v ≠ 0) :
    A • Projectivization.mk (ZMod q) v hv =
      Projectivization.mk (ZMod q) ((A : Matrix (Fin 2) (Fin 2) (ZMod q)) *ᵥ v)
        (mulVec_ne_zero q A v hv) := by
  change (Matrix.GeneralLinearGroup.toLin A) • (Projectivization.mk (ZMod q) v hv) = _
  rw [Projectivization.smul_mk]
  congr 1

p2m_export "SteinbergQuotAux" "smul_mk"

def infty : ProjLine q := Projectivization.mk (ZMod q) ![1, 0] (by simp)

def aff (x : ZMod q) : ProjLine q := Projectivization.mk (ZMod q) ![x, 1] (by simp)

theorem aff_injective : Function.Injective (aff q) := by
  intro x y h
  rw [aff, aff, Projectivization.mk_eq_mk_iff'] at h
  obtain ⟨a, ha⟩ := h
  have h1 := congrFun ha 1
  have h0 := congrFun ha 0
  simp at h1 h0
  rw [h1, one_mul] at h0
  exact h0.symm

theorem aff_ne_infty (x : ZMod q) : aff q x ≠ infty q := by
  intro h
  rw [aff, infty, Projectivization.mk_eq_mk_iff'] at h
  obtain ⟨a, ha⟩ := h
  have h1 := congrFun ha 1
  simp at h1

theorem eq_infty_or_eq_aff (pt : ProjLine q) : pt = infty q ∨ ∃ x, pt = aff q x := by
  induction pt using Projectivization.ind with
  | h v hv =>
    by_cases h1 : v 1 = 0
    · left
      rw [infty, Projectivization.mk_eq_mk_iff']
      refine ⟨v 0, ?_⟩
      ext i; fin_cases i
      · simp
      · simp [h1]
    · right
      refine ⟨v 0 * (v 1)⁻¹, ?_⟩
      rw [aff, Projectivization.mk_eq_mk_iff']
      refine ⟨v 1, ?_⟩
      ext i; fin_cases i
      · simp; field_simp
      · simp

theorem unipotent_smul_aff (t x : ZMod q) : unipotent q t • aff q x = aff q (x + t) := by
  rw [aff, aff, smul_mk]
  congr 1
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]

theorem unipotent_smul_infty (t : ZMod q) : unipotent q t • infty q = infty q := by
  rw [infty, smul_mk]
  congr 1
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

noncomputable def chart : Unit ⊕ ZMod q ≃ ProjLine q :=
  Equiv.ofBijective (Sum.elim (fun _ => infty q) (aff q)) (by
    constructor
    · rintro (a | a) (b | b) h
      · rfl
      · exact absurd h (aff_ne_infty q b).symm
      · exact absurd h (aff_ne_infty q a)
      · simp only [Sum.elim_inr] at h
        rw [aff_injective q h]
    · intro pt
      rcases eq_infty_or_eq_aff q pt with h | ⟨x, h⟩
      · exact ⟨Sum.inl (), h.symm⟩
      · exact ⟨Sum.inr x, h.symm⟩)

@[scoped simp] theorem chart_inl (a : Unit) : chart q (Sum.inl a) = infty q := rfl
@[scoped simp] theorem chart_inr (x : ZMod q) : chart q (Sum.inr x) = aff q x := rfl

@[scoped simp] theorem chart_symm_infty : (chart q).symm (infty q) = Sum.inl () := by
  rw [Equiv.symm_apply_eq]; rfl

@[scoped simp] theorem chart_symm_aff (x : ZMod q) : (chart q).symm (aff q x) = Sum.inr x := by
  rw [Equiv.symm_apply_eq]; rfl

theorem translate_pow_apply (n : ℕ) (x : ZMod q) :
    ((Equiv.addRight (1 : ZMod q)) ^ n) x = x + n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, Equiv.coe_addRight, ih]
    push_cast; ring

variable (k : Type*) [Field k]

theorem charpoly_lmapDomain_translate :
    (Finsupp.lmapDomain k k (fun x : ZMod q => x + 1)).charpoly = X ^ q - 1 := by
  have h := charpoly_lmapDomain_of_transitive k (S := ZMod q) (Equiv.addRight (1 : ZMod q))
    (fun x y => ⟨(y - x).val, by
      rw [Equiv.Perm.smul_def, translate_pow_apply, ZMod.natCast_zmod_val]; ring⟩)
  rw [Nat.card_zmod] at h
  rw [← h]
  rfl

theorem charpoly_ind_unipotent_one :
    (ind q k (unipotent q 1)).charpoly = (X - 1) * (X ^ q - 1) := by
  classical

  set E : (ProjLine q →₀ k) ≃ₗ[k] (Unit →₀ k) × (ZMod q →₀ k) :=
    (Finsupp.domLCongr (chart q).symm).trans (Finsupp.sumFinsuppLEquivProdFinsupp k) with hE
  have hconj : E.conj (ind q k (unipotent q 1)) =
      LinearMap.prodMap LinearMap.id (Finsupp.lmapDomain k k (fun x : ZMod q => x + 1)) := by
    apply LinearMap.prod_ext
    · apply Finsupp.lhom_ext
      intro a c
      simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.inl_apply,
        LinearMap.prodMap_apply, LinearMap.id_apply, map_zero, LinearEquiv.coe_coe]
      have h1 : E.symm (Finsupp.single a c, 0) = Finsupp.single (infty q) c := by
        rw [LinearEquiv.symm_apply_eq]
        simp [E, Finsupp.domLCongr_apply, Finsupp.sumFinsuppLEquivProdFinsupp,
          Finsupp.equivMapDomain_single]
      rw [h1, Representation.ofMulActionFinsupp_single,
        unipotent_smul_infty, ← h1, LinearEquiv.apply_symm_apply]
    · apply Finsupp.lhom_ext
      intro x c
      simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.inr_apply,
        LinearMap.prodMap_apply, map_zero, LinearEquiv.coe_coe,
        Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      have h1 : ∀ y : ZMod q, E.symm (0, Finsupp.single y c) = Finsupp.single (aff q y) c := by
        intro y
        rw [LinearEquiv.symm_apply_eq]
        simp [E, Finsupp.domLCongr_apply, Finsupp.sumFinsuppLEquivProdFinsupp,
          Finsupp.equivMapDomain_single]
      rw [h1, Representation.ofMulActionFinsupp_single,
        unipotent_smul_aff, ← h1, LinearEquiv.apply_symm_apply]
  rw [← LinearEquiv.charpoly_conj E, hconj, LinearMap.charpoly_prodMap,
    charpoly_lmapDomain_translate, ← Module.End.one_eq_id, LinearMap.charpoly_one]
  simp

theorem torus_val_mulVec (α : (GaloisField q 2)ˣ) (x : GaloisField q 2) :
    ((torus q α : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) *ᵥ ⇑((quadBasis q).repr x) =
      ⇑((quadBasis q).repr ((α : GaloisField q 2) * x)) := by
  have h : ((torus q α : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) =
      LinearMap.toMatrix (quadBasis q) (quadBasis q)
        (LinearMap.mulLeft (ZMod q) (α : GaloisField q 2)) := by
    rfl
  rw [h, LinearMap.toMatrix_mulVec_repr]
  rfl

theorem exists_singer : ∃ g₀ : GL2 q, ∀ x y : ProjLine q, ∃ n : ℕ, g₀ ^ n • x = y := by
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := (GaloisField q 2)ˣ)
  refine ⟨torus q ζ, fun x y => ?_⟩
  set b := quadBasis q with hb

  set a : GaloisField q 2 := b.equivFun.symm x.rep with ha
  set c : GaloisField q 2 := b.equivFun.symm y.rep with hc
  have ha0 : a ≠ 0 := (LinearEquiv.map_ne_zero_iff b.equivFun.symm).mpr x.rep_nonzero
  have hc0 : c ≠ 0 := (LinearEquiv.map_ne_zero_iff b.equivFun.symm).mpr y.rep_nonzero
  have hxa : ⇑(b.repr a) = x.rep := by
    rw [← Module.Basis.equivFun_apply, ha, LinearEquiv.apply_symm_apply]
  have hyc : ⇑(b.repr c) = y.rep := by
    rw [← Module.Basis.equivFun_apply, hc, LinearEquiv.apply_symm_apply]

  have hmem : Units.mk0 (c * a⁻¹) (mul_ne_zero hc0 (inv_ne_zero ha0)) ∈ Submonoid.powers ζ := by
    rw [(isOfFinOrder_of_finite ζ).mem_powers_iff_mem_zpowers]
    exact hζ _
  obtain ⟨n, hn⟩ := hmem
  simp only at hn
  refine ⟨n, ?_⟩
  have key : ((torus q ζ ^ n : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) *ᵥ x.rep = y.rep := by
    rw [← map_pow, ← hxa, torus_val_mulVec, hn, Units.val_mk0, inv_mul_cancel_right₀ ha0, hyc]
  conv_lhs => rw [← x.mk_rep]
  rw [smul_mk, ← y.mk_rep]
  congr 1

theorem unipotent_add (s t : ZMod q) : unipotent q s * unipotent q t = unipotent q (s + t) := by
  apply Units.ext
  simp only [Units.val_mul, unipotent_val]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem unipotent_zero : unipotent q 0 = 1 := by
  apply Units.ext
  simp only [unipotent_val, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem unipotent_one_pow (n : ℕ) : unipotent q 1 ^ n = unipotent q n := by
  induction n with
  | zero => simp [unipotent_zero]
  | succ n ih => rw [pow_succ, ih, unipotent_add]; push_cast; rfl

theorem unipotent_one_pow_q : unipotent q 1 ^ q = 1 := by
  rw [unipotent_one_pow, ZMod.natCast_self, unipotent_zero]

theorem unipotent_one_mul_diagElem_inv (a : (ZMod q)ˣ) :
    unipotent q 1 * diagElem q a⁻¹ = diagElem q a⁻¹ * unipotent q 1 ^ (a : ZMod q).val := by
  rw [unipotent_one_pow, ZMod.natCast_zmod_val]
  apply Units.ext
  change !![(1 : ZMod q), 1; 0, 1] * !![((a⁻¹ : (ZMod q)ˣ) : ZMod q), 0; 0, 1] =
    !![((a⁻¹ : (ZMod q)ˣ) : ZMod q), 0; 0, 1] * !![1, (a : ZMod q); 0, 1]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, -ZMod.inv_coe_unit]

theorem ind_constFun (g : GL2 q) : ind q k g (constFun q k) = constFun q k := by
  rw [Representation.ofMulActionFinsupp_def, Finsupp.lmapDomain_apply]
  ext y
  have : y = g • (g⁻¹ • y) := (smul_inv_smul g y).symm
  conv_lhs => rw [this]
  rw [Finsupp.mapDomain_apply (MulAction.injective g)]
  simp [constFun]

theorem coeffSum_ind (g : GL2 q) (v : ProjLine q →₀ k) :
    coeffSum q k (ind q k g v) = coeffSum q k v := by
  rw [Representation.ofMulActionFinsupp_def, Finsupp.lmapDomain_apply, coeffSum,
    Finsupp.linearCombination_mapDomain]
  rfl

theorem coeffSum_surjective : Function.Surjective (coeffSum q k) := by
  intro c
  refine ⟨Finsupp.single (infty q) c, ?_⟩
  simp [coeffSum, Finsupp.linearCombination_single]

theorem finrank_steinberg : Module.finrank k (steinberg q k).toSubmodule = q := by
  classical
  have h := LinearMap.finrank_range_add_finrank_ker (coeffSum q k)
  rw [LinearMap.range_eq_top.mpr (coeffSum_surjective q k), finrank_top, Module.finrank_self,
    finrank_ind] at h
  change Module.finrank k (LinearMap.ker (coeffSum q k)) = q
  omega

theorem constFun_ne_zero : constFun q k ≠ 0 := by
  intro h
  have := congrArg (fun f : ProjLine q →₀ k => f (infty q)) h
  simp [constFun] at this

end SteinbergQuotAux
p2m_reactivate "P2MW.S_CuspidalType_exists_surjective_steinberg_toSubmodule_eq_zero_iff_smul_constFun_of_charpoly_ind_eq_X_sub_one_sq_mul.SteinbergQuotAux"

open SteinbergQuotAux in
theorem solution
    {q : ℕ} [Fact q.Prime] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (κ : Type) [Field κ] [CharP κ p]
    {V : Type} [AddCommGroup V] [Module κ V] [FiniteDimensional κ V] (ρ : Representation κ (CuspidalType.GL2 q) V)
    (hρ : ∀ g : CuspidalType.GL2 q,
      LinearMap.charpoly (CuspidalType.ind q κ g) = (X - 1) ^ 2 * LinearMap.charpoly (ρ g)) :
    ∃ π : ↥(CuspidalType.steinberg q κ).toSubmodule →ₗ[κ] V,
      (∀ g : CuspidalType.GL2 q, ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
        π ⟨CuspidalType.ind q κ g v, (CuspidalType.steinberg q κ).apply_mem_toSubmodule g v.2⟩ = ρ g (π v)) ∧
      Function.Surjective π ∧
      ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
        π v = 0 ↔ ∃ c : κ, (v : CuspidalType.ProjLine q →₀ κ) = c • CuspidalType.constFun q κ := by
  classical

  set N := (ProjLine q →₀ κ) with hN
  set St : Submodule κ (ProjLine q →₀ κ) := (steinberg q κ).toSubmodule with hSt
  set stRep : Representation κ (GL2 q) St := (steinberg q κ).toRepresentation with hstRep
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le

  have hq1 : (q : κ) + 1 = 0 := by
    obtain ⟨g₀, hg₀⟩ := exists_singer q
    have h1 : (ind q κ g₀).charpoly = X ^ (q + 1) - 1 := by
      rw [Representation.ofMulActionFinsupp_def, charpoly_lmapDomain_of_transitive κ g₀ hg₀, card_projLine]
    have h2 := hρ g₀
    rw [h1] at h2
    have h3 := congrArg (fun P : κ[X] => (derivative P).eval 1) h2
    simp only [derivative_sub, derivative_one, sub_zero, derivative_mul,
      derivative_pow, derivative_X, eval_mul, eval_C, eval_pow, eval_sub, eval_X, eval_one, sub_self,
      eval_add, Nat.cast_ofNat, one_pow, mul_one, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul, add_zero,
      Nat.succ_sub_one, pow_one] at h3
    exact_mod_cast h3
  have hq0 : (q : κ) ≠ 0 := by
    intro h; rw [h, zero_add] at hq1; exact one_ne_zero hq1

  have hfinV : Module.finrank κ V = q - 1 := by
    have := finrank_eq_of_charpoly_eq (ρ 1) (ind q κ 1) (hρ 1)
    rw [finrank_ind] at this
    omega
  have htrV : ∀ g, LinearMap.trace κ N (ind q κ g) = LinearMap.trace κ V (ρ g) + 2 := fun g =>
    trace_eq_of_charpoly_eq (ρ g) (ind q κ g) (hρ g)
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := κ) (by rw [hfinV]; omega)

  have hfixV : ∀ v : V, ρ (unipotent q 1) v = v → v = 0 := by
    have h1 := hρ (unipotent q 1)
    rw [charpoly_ind_unipotent_one, pow_two, mul_assoc] at h1
    have h2 := mul_left_cancel₀ (X_sub_C_ne_zero (1 : κ)) (by simpa using h1)

    have h3 : (ρ (unipotent q 1)).charpoly = ∑ i ∈ Finset.range q, X ^ i := by
      have h4 : (X - 1 : κ[X]) * (ρ (unipotent q 1)).charpoly = (X - 1) * ∑ i ∈ Finset.range q, X ^ i := by
        rw [← h2, mul_comm, geom_sum_mul]
      exact mul_left_cancel₀ (by simpa using X_sub_C_ne_zero (1 : κ)) h4
    have h5 : ¬ Module.End.HasEigenvalue (ρ (unipotent q 1)) 1 := by
      rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, h3, IsRoot.def, eval_finsetSum]
      simp only [eval_pow, eval_X, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        mul_one]
      exact hq0
    intro v hv
    by_contra hv0
    exact h5 (Module.End.hasEigenvalue_of_hasEigenvector ⟨by
      rw [Module.End.mem_eigenspace_iff, one_smul]; exact hv, hv0⟩)

  have hspanV : Submodule.span κ (Set.range ⇑ρ) = ⊤ := by
    set K := AlgebraicClosure κ with hK

    let ρK : Representation K (GL2 q) (K ⊗[κ] V) :=
      { toFun := fun g => (ρ g).baseChange K
        map_one' := by rw [map_one, Module.End.one_eq_id, LinearMap.baseChange_id]; rfl
        map_mul' := fun g h => by
          rw [map_mul, Module.End.mul_eq_comp, LinearMap.baseChange_comp]; rfl }
    have hρK : ∀ g, ρK g = (ρ g).baseChange K := fun g => rfl

    have hfixK : ∀ w : K ⊗[κ] V, ρK (unipotent q 1) w = w → w = 0 := by
      set f₁ : V →ₗ[κ] V := ρ (unipotent q 1) - LinearMap.id with hf₁
      have hinj : Function.Injective f₁ := by
        intro v w hvw
        rw [← sub_eq_zero, ← map_sub] at hvw
        have := hfixV (v - w) (by simpa [f₁, sub_eq_zero] using hvw)
        exact sub_eq_zero.mp this
      set e₁ := LinearEquiv.ofInjectiveEndo f₁ hinj with he₁
      have he₁' : (e₁ : V →ₗ[κ] V) = f₁ := rfl
      have hK1 : (ρK (unipotent q 1) - LinearMap.id : K ⊗[κ] V →ₗ[K] K ⊗[κ] V) =
          (e₁.baseChange κ K V V : K ⊗[κ] V →ₗ[K] K ⊗[κ] V) := by
        rw [hρK, LinearEquiv.coe_baseChange, he₁', hf₁, LinearMap.baseChange_sub,
          LinearMap.baseChange_id]
      intro w hw
      have h1 : (ρK (unipotent q 1) - LinearMap.id : K ⊗[κ] V →ₗ[K] K ⊗[κ] V) w = 0 := by
        rw [LinearMap.sub_apply, hw, LinearMap.id_apply, sub_self]
      rw [hK1] at h1
      exact (LinearEquiv.map_eq_zero_iff _).mp h1

    haveI hirr : ρK.IsIrreducible := by
      have hfinK : Module.finrank K (K ⊗[κ] V) = q - 1 := by rw [Module.finrank_baseChange, hfinV]
      haveI : Nontrivial (K ⊗[κ] V) := Module.nontrivial_of_finrank_pos (R := K) (by rw [hfinK]; omega)
      haveI : Nontrivial (Subrepresentation ρK) := ⟨⟨⊥, ⊤, fun h =>
        bot_ne_top (α := Submodule K (K ⊗[κ] V)) (congrArg Subrepresentation.toSubmodule h)⟩⟩
      refine ⟨fun W => ?_⟩
      · by_cases hW : W = ⊥
        · exact Or.inl hW
        · right
          have hW' : W.toSubmodule ≠ ⊥ := fun h => hW (Subrepresentation.toSubmodule_injective h)
          have hle := sub_one_le_finrank_of_stable q (ρK (unipotent q 1))
            (fun a => ρK (diagElem q a⁻¹))
            (by rw [← map_pow, unipotent_one_pow_q, map_one])
            (fun a => by rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_pow,
              ← map_mul, ← map_mul, unipotent_one_mul_diagElem_inv])
            (fun a => (ρK.apply_bijective _).1)
            W.toSubmodule (fun w hw => W.apply_mem_toSubmodule _ hw)
            (fun a w hw => W.apply_mem_toSubmodule _ hw) hW' (fun w _ hw => hfixK w hw)
          apply Subrepresentation.toSubmodule_injective
          change W.toSubmodule = ⊤
          apply Submodule.eq_top_of_finrank_eq
          exact le_antisymm (Submodule.finrank_le _) (hfinK ▸ hle)
    have hspanK := Representation.span_range_eq_top_of_isIrreducible ρK

    apply eq_top_of_span_baseChange_eq_top K
    apply top_le_iff.mp
    rw [← hspanK]
    apply Submodule.span_mono
    rintro _ ⟨g, rfl⟩
    exact ⟨ρ g, Submodule.subset_span ⟨g, rfl⟩, rfl⟩

  have hfinN : Module.finrank κ N = Module.finrank κ V + 2 :=
    finrank_eq_of_charpoly_eq (ρ 1) (ind q κ 1) (hρ 1)
  exact exists_of_span_eq_top (ind q κ) St (fun g v hv => (steinberg q κ).apply_mem_toSubmodule g hv)
    (coeffSum q κ) (fun v => LinearMap.mem_ker) (coeffSum_ind q κ) (coeffSum_surjective q κ)
    (constFun q κ) (constFun_ne_zero q κ) ((constFun_mem_steinberg_iff q κ).mpr hq1)
    (ind_constFun q κ) ρ hspanV htrV hfinN

end S_CuspidalType_exists_surjective_steinberg_toSubmodule_eq_zero_iff_smul_constFun_of_charpoly_ind_eq_X_sub_one_sq_mul
end P2MW
export P2MW.S_CuspidalType_exists_surjective_steinberg_toSubmodule_eq_zero_iff_smul_constFun_of_charpoly_ind_eq_X_sub_one_sq_mul (solution)
