-- Prove2me | solution 1 for GOSNIZK.CircuitSound.knowledge_extraction
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:38:10.157738+00:00
-- url     : https://prove2.me/submissions/71202530-51b4-433d-b8d0-852f3e03f04b

import Mathlib
import Definitions.Def_GOSNIZK_CircuitSound_Protocol

set_option autoImplicit false
open GOSNIZK.CircuitSound

namespace GOSAux

variable {N : ℕ} {R C CK XK TK Rp Prf : Type} [AddCommGroup R] [CommGroup C]
  (S : Scheme N R C CK XK TK Rp Prf)

lemma one_ne (hN : 2 ≤ N) : (1 : ZMod N) ≠ 0 := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  exact one_ne_zero

lemma ofBit_inj (hN : 2 ≤ N) {a b : Bool} (h : (ofBit a : ZMod N) = ofBit b) : a = b := by
  have h1 := one_ne hN
  cases a <;> cases b <;> simp [ofBit] at h ⊢
  · exact h1 h.symm
  · exact h1 h

lemma gate_eq (hhom : S.Homomorphic) (ck : CK) (hk : S.IsKey ck) (m₀ m₁ m₂ : ZMod N)
    (r₀ r₁ r₂ : R) :
    S.gateCom ck (S.com ck m₀ r₀) (S.com ck m₁ r₁) (S.com ck m₂ r₂) =
      S.com ck (m₀ + m₁ + 2 * m₂ - 2) (r₀ + r₁ + 2 • r₂) := by
  unfold Scheme.gateCom
  have h2 : S.com ck m₂ r₂ ^ 2 = S.com ck (m₂ + m₂) (r₂ + r₂) := by
    rw [hhom ck hk, sq]
  rw [h2, ← hhom ck hk, ← hhom ck hk, ← hhom ck hk]
  have e1 : m₀ + m₁ + (m₂ + m₂) + -2 = m₀ + m₁ + 2 * m₂ - 2 := by ring
  have e2 : r₀ + r₁ + (r₂ + r₂) + 0 = r₀ + r₁ + 2 • r₂ := by rw [two_nsmul]; abel
  rw [e1, e2]

lemma bits_of_mem (hN : 4 ≤ N) (b₀ b₁ b₂ b : Bool)
    (h : (ofBit b₀ + ofBit b₁ + 2 * ofBit b₂ - 2 : ZMod N) = ofBit b) : b₂ = !(b₀ && b₁) := by
  have h1 : (1 : ZMod N) ≠ 0 := one_ne (by omega)
  have h2 : (2 : ZMod N) ≠ 0 := by
    have := (ZMod.natCast_eq_zero_iff 2 N).not.mpr (by
      intro h; have := Nat.le_of_dvd two_pos h; omega)
    simpa using this
  have h3 : (3 : ZMod N) ≠ 0 := by
    have := (ZMod.natCast_eq_zero_iff 3 N).not.mpr (by
      intro h; have := Nat.le_of_dvd (by norm_num) h; omega)
    simpa using this
  cases b₀ <;> cases b₁ <;> cases b₂ <;> cases b <;> simp only [ofBit, Bool.false_eq_true, ↓reduceIte] at h ⊢ <;> first
    | rfl
    | (exfalso; first
        | exact h1 (by linear_combination h)
        | exact h1 (by linear_combination -h)
        | exact h2 (by linear_combination h)
        | exact h2 (by linear_combination -h)
        | exact h3 (by linear_combination h)
        | exact h3 (by linear_combination -h))

lemma gate_sound (hN : 4 ≤ N) (hhom : S.Homomorphic) (hbind : S.PerfectBinding)
    (hsound01 : S.PerfectSoundness01) (ck : CK) (xk : XK) (hk : (ck, xk) ∈ S.Kbind.support)
    (b₀ b₁ b₂ : Bool) (r₀ r₁ r₂ : R) (π : Prf)
    (h : S.V01 ck (S.gateCom ck (S.com ck (ofBit b₀) r₀) (S.com ck (ofBit b₁) r₁)
      (S.com ck (ofBit b₂) r₂)) π = true) : b₂ = !(b₀ && b₁) := by
  rw [gate_eq S hhom ck (Or.inl ⟨xk, hk⟩)] at h
  obtain ⟨b, r, hbr⟩ := hsound01 ck xk hk _ _ h
  have hm : (ofBit b₀ + ofBit b₁ + 2 * ofBit b₂ - 2 : ZMod N) = ofBit b := by
    by_contra hne
    exact hbind ck xk hk _ _ _ _ hne hbr
  exact bits_of_mem hN b₀ b₁ b₂ b hm

lemma verify_bits (hN : 4 ≤ N) (hhom : S.Homomorphic) (hbind : S.PerfectBinding)
    (hsound01 : S.PerfectSoundness01) (ck : CK) (xk : XK) (hk : (ck, xk) ∈ S.Kbind.support)
    {n : ℕ} (Γ : Circuit n) (π : Proof C Prf Γ) (hV : S.Verify ck Γ π) :
    ∃ b : Fin n → Bool, Γ.Sat b ∧ ∀ i, ∃ r, π.c i = S.com ck (ofBit (b i)) r := by
  obtain ⟨hout, hw, hg⟩ := hV
  have hex : ∀ i, ∃ (b : Bool) (r : R), π.c i = S.com ck (ofBit b) r :=
    fun i => hsound01 ck xk hk _ _ (hw i)
  choose b r hbr using hex
  refine ⟨b, ⟨?_, ?_⟩, fun i => ⟨r i, hbr i⟩⟩
  · intro g hg'
    obtain ⟨gi, hgi, rfl⟩ := List.mem_iff_getElem.mp hg'
    have h := hg ⟨gi, hgi⟩
    simp only [Fin.getElem_fin, hbr] at h
    exact gate_sound S hN hhom hbind hsound01 ck xk hk _ _ _ _ _ _ _ h
  · have h1 : S.com ck (ofBit (b Γ.out)) (r Γ.out) = S.com ck (ofBit true) 0 := by
      rw [← hbr, hout]; simp [ofBit]
    have h2 : (ofBit (b Γ.out) : ZMod N) = ofBit true := by
      by_contra hne
      exact hbind ck xk hk _ _ _ _ hne h1
    exact ofBit_inj (by omega) h2

lemma completeness_aux (hhom : S.Homomorphic) (hcomp01 : S.PerfectCompleteness01) :
    S.CircuitPerfectCompleteness := by
  intro ck hk n Γ w hsat r ρw ρg
  have hc : ∀ i, (S.prove ck Γ w r ρw ρg).c i
      = S.com ck (ofBit (w i)) (Scheme.wireRand Γ r i) := by
    intro i
    by_cases hi : i = Γ.out
    · subst hi
      simp [Scheme.prove, Scheme.wireRand, ofBit, hsat.2]
    · simp [Scheme.prove, Scheme.wireRand, hi]
  refine ⟨?_, ?_, ?_⟩
  · simp [Scheme.prove]
  · intro i
    rw [hc i]
    exact hcomp01 ck hk (w i) _ (ρw i)
  · intro g
    have hg := hsat.1 _ (List.getElem_mem g.2)
    rw [hc, hc, hc, gate_eq S hhom ck hk]
    obtain ⟨b', hb'⟩ : ∃ b' : Bool, (ofBit (w Γ.gates[g].1) + ofBit (w Γ.gates[g].2.1)
        + 2 * ofBit (w Γ.gates[g].2.2) - 2 : ZMod N) = ofBit b' := by
      generalize w Γ.gates[g].1 = a at hg ⊢
      generalize w Γ.gates[g].2.1 = c at hg ⊢
      generalize w Γ.gates[g].2.2 = d at hg ⊢
      subst hg
      cases a <;> cases c
      · exact ⟨false, by simp [ofBit] <;> ring⟩
      · exact ⟨true, by simp [ofBit] <;> ring⟩
      · exact ⟨true, by simp [ofBit] <;> ring⟩
      · exact ⟨false, by simp [ofBit] <;> ring⟩
    have := hcomp01 ck hk b' (Scheme.wireRand Γ r Γ.gates[g].1 + Scheme.wireRand Γ r Γ.gates[g].2.1
      + 2 • Scheme.wireRand Γ r Γ.gates[g].2.2) (ρg g)
    rw [← hb'] at this
    exact this

lemma soundness_aux (hN : 4 ≤ N) (hhom : S.Homomorphic) (hbind : S.PerfectBinding)
    (hsound01 : S.PerfectSoundness01) : S.CircuitPerfectSoundness := by
  intro ck xk hk n Γ hunsat π hV
  obtain ⟨b, hb, -⟩ := verify_bits S hN hhom hbind hsound01 ck xk hk Γ π hV
  exact hunsat ⟨b, hb⟩

lemma extraction_aux (hN : 4 ≤ N) (hhom : S.Homomorphic) (hbind : S.PerfectBinding)
    (hsound01 : S.PerfectSoundness01) (hext : S.PerfectExtractability) :
    S.CircuitPerfectKnowledgeExtraction := by
  intro ck xk hk n Γ π hV
  obtain ⟨b, hb, hc⟩ := verify_bits S hN hhom hbind hsound01 ck xk hk Γ π hV
  have h1 : (1 : ZMod N) ≠ 0 := one_ne (by omega)
  have : S.extract xk π = b := by
    funext i
    obtain ⟨r, hr⟩ := hc i
    simp only [Scheme.extract, hr, hext ck xk hk (b i) r]
    cases b i <;> simp [ofBit, Ne.symm h1]
  rw [this]
  exact hb

end GOSAux

open GOSAux

theorem solution {N : ℕ} {R C CK XK TK Rp Prf : Type} [AddCommGroup R] [Fintype R] [CommGroup C] [Fintype C]
    [Fintype Rp] [Nonempty Rp] (S : Scheme N R C CK XK TK Rp Prf)
    (hN : 4 ≤ N) (hhom : S.Homomorphic) (hbind : S.PerfectBinding)
    (hsound01 : S.PerfectSoundness01) (hext : S.PerfectExtractability) :
    S.CircuitPerfectKnowledgeExtraction := by
  exact extraction_aux S hN hhom hbind hsound01 hext
